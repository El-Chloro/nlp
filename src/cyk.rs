use crate::grammar::Grammar;
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct ChartEntry {
    probability: f64,
    backpointer: Option<BackPointer>,
}

#[derive(Debug, Clone)]
enum BackPointer {
    Terminal(String), 
    Unary {
        child_non_terminal: String, 
    },
    Binary {
        split_point: usize, 
        left_child_non_terminal: String, 
        right_child_non_terminal: String,
    }
}

type Chart = Vec<Vec<HashMap<String, ChartEntry>>>;

pub fn parse_sentence(grammar: &Grammar, words: &[String], start_symbol: &str) -> String {
    let n = words.len();
    if n == 0 {
        return "(NOPARSE)".to_string();
    }

    // Initialize empty chart
    let default_cell: HashMap<String, ChartEntry> = HashMap::new();
    let mut chart: Chart = vec![vec![default_cell.clone(); n + 1]; n + 1];

    // Fill chart with lexical rules for individual words
    for i in 0..n {
        let word = &words[i];
        let j = i + 1; 

        if let Some(rules) = grammar.lexical_rules_by_rhs.get(word) {
            for rule in rules {
                let entry = chart[j][i].entry(rule.lhs.clone()).or_insert_with(|| ChartEntry {
                    probability: 0.0,
                    backpointer: None,
                });
                if rule.probability > entry.probability {
                    entry.probability = rule.probability;
                    entry.backpointer = Some(BackPointer::Terminal(rule.lhs.clone()));
                }
            }
        }
        
        apply_unary_closure(grammar, &mut chart[j][i]);
    }

    //  Main CYK loop: fill cells for spans of length > 1
    for r in 2..=n { 
        for i in 0..=(n - r) { 
            let j = i + r; 

            let mut cell_updates: HashMap<String, ChartEntry> = HashMap::new();
            
            for m in (i + 1)..j {
                // Get All nonterminals wiht positive probabilities 
                let left_span_entries: Vec<(String, f64)> = chart[m][i]
                    .iter().filter(|(_, e)| e.probability > 0.0).map(|(nt, e)| (nt.clone(), e.probability)).collect();
                let right_span_entries: Vec<(String, f64)> = chart[j][m]
                    .iter().filter(|(_, e)| e.probability > 0.0).map(|(nt, e)| (nt.clone(), e.probability)).collect();

                // Try all binary rules A → B C
                for (b_nt, b_prob) in &left_span_entries {
                    for (c_nt, c_prob) in &right_span_entries {
                        if let Some(rules) = grammar.binary_rules_by_children.get(&(b_nt.clone(), c_nt.clone())) {
                            for rule in rules {
                                let new_prob = rule.probability * b_prob * c_prob;
                                let a_nt = rule.lhs.clone();

                                let current_best_in_cell_updates = cell_updates.entry(a_nt.clone()).or_insert_with(|| ChartEntry {
                                    probability: 0.0, backpointer: None,
                                });

                                if new_prob > current_best_in_cell_updates.probability {
                                    current_best_in_cell_updates.probability = new_prob;
                                    current_best_in_cell_updates.backpointer = Some(BackPointer::Binary {
                                        split_point: m,
                                        left_child_non_terminal: b_nt.clone(),
                                        right_child_non_terminal: c_nt.clone(),
                                    });
                                }
                            }
                        }
                    }
                }
            } 

            // iF start symbol derives the whole sentence, build parse tree
            let target_cell = &mut chart[j][i];
            for (nt_from_update, entry_from_update) in cell_updates {
                if entry_from_update.probability > 0.0 { 
                    let current_target_entry = target_cell.entry(nt_from_update.clone()).or_insert_with(|| ChartEntry {
                        probability: 0.0, backpointer: None,
                    });
                    if entry_from_update.probability > current_target_entry.probability {
                        *current_target_entry = entry_from_update;
                    }
                }
            }
            
            apply_unary_closure(grammar, target_cell);
        } 
    } 

    // Check if start symbol exists in highest chart cell 
    if let Some(final_entry) = chart[n][0].get(start_symbol) {
        if final_entry.probability > 0.0 {
            return reconstruct_tree(&chart, start_symbol, 0, n, words);
        }
    }

    format!("(NOPARSE {})", words.join(" "))
}

fn apply_unary_closure(grammar: &Grammar, cell: &mut HashMap<String, ChartEntry>) {
     let mut changed = true;
     while changed { 
        changed = false;
        // Collect updates to avoid changing the map while iterating
        let mut additions: Vec<(String, ChartEntry)> = Vec::new();

        for (b_nt, b_entry) in cell.iter() {
            if b_entry.probability == 0.0 { continue; }

             if let Some(unary_rules) = grammar.unary_rules_by_rhs.get(b_nt) {
                 for rule in unary_rules {
                     let new_prob = rule.probability * b_entry.probability;
                     let a_nt = &rule.lhs; 

                     let current_prob_a = cell.get(a_nt).map_or(0.0, |e| e.probability);

                     // If this path to A is better, prepare an update
                     if new_prob > current_prob_a {
                         let new_entry_a = ChartEntry {
                             probability: new_prob,
                             backpointer: Some(BackPointer::Unary {
                                 child_non_terminal: b_nt.clone(), 
                             }),
                         };
                         additions.push((a_nt.clone(), new_entry_a));
                         changed = true; 
                     }
                 }
             }
        }
        for (nt, entry) in additions {
            cell.insert(nt, entry);
        }
     }
}

// rekursive reconstruction of the parse tree from the completed CYK chart
fn reconstruct_tree(
    chart: &Chart,
    non_terminal: &str, 
    i: usize, 
    j: usize, 
    words: &[String]
) -> String {
    let entry = chart[j][i].get(non_terminal)
                     .unwrap_or_else(|| panic!("reconstruct_tree: NT '{}' not found in chart for span ({},{})", non_terminal, i, j));

    match entry.backpointer.as_ref().expect("reconstruct_tree: Missing backpointer") {
        BackPointer::Terminal(_) => {
            //  A -> word
             format!("({} {})", non_terminal, words[i])
        }
        BackPointer::Unary { child_non_terminal } => {
            // A -> B
             let child_tree = reconstruct_tree(chart, child_non_terminal, i, j, words);
             format!("({} {})", non_terminal, child_tree)
        }
        BackPointer::Binary { split_point, left_child_non_terminal, right_child_non_terminal } => {
            //  A -> B C
             let m = *split_point; 
             let left_tree = reconstruct_tree(chart, left_child_non_terminal, i, m, words);
             let right_tree = reconstruct_tree(chart, right_child_non_terminal, m, j, words);
             format!("({} {} {})", non_terminal, left_tree, right_tree)
        }
    }
}
