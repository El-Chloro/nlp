use crate::grammar::Grammar;
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct ChartEntry {
    probability: f64,
    backpointer: Option<BackPointer>,
}

#[derive(Debug, Clone)]
enum BackPointer {
    Terminal,
    Unary {
        child_non_terminal_id: usize,
    },
    Binary {
        split_point: usize,
        left_child_non_terminal_id: usize,
        right_child_non_terminal_id: usize,
    }
}

type Chart = Vec<Vec<HashMap<usize, ChartEntry>>>;

pub fn parse_sentence(grammar: &Grammar, words: &[String], start_symbol_str: &str) -> String {
    let n = words.len();
    if n == 0 {
        return "(NOPARSE)".to_string();
    }

    // Get ID for start symbol string
    let start_symbol_id = match grammar.non_terminal_to_id.get(start_symbol_str) {
        Some(id) => *id,
        None => {
            return format!("(NOPARSE Error: Start symbol '{}' not found in grammar)", start_symbol_str);
        }
    };

    // Initialize empty chart
    let mut chart: Chart = vec![vec![HashMap::new(); n + 1]; n + 1];

    // Fill chart with lexical rules for individual words
    for i in 0..n {
        let word = &words[i];
        let j = i + 1;

        if let Some(rules) = grammar.lexical_rules_by_rhs.get(word) {
            for rule in rules { 
                let entry = chart[j][i].entry(rule.lhs_id).or_insert_with(|| ChartEntry {
                    probability: 0.0,
                    backpointer: None,
                });
                if rule.probability > entry.probability {
                    entry.probability = rule.probability;
                    entry.backpointer = Some(BackPointer::Terminal); 
                }
            }
        }

        apply_unary_closure(grammar, &mut chart[j][i]);
    }

    //  Main CYK loop: fill cells for spans of length > 1
    for r in 2..=n { // r: span length 
        for i in 0..=(n - r) { // i: span start 
            let j = i + r; // j: span end 

            let mut cell_updates: HashMap<usize, ChartEntry> = HashMap::new();

            for m in (i + 1)..j { // m: split point
                // Get All nonterminals wiht positive probabilities 
                let left_span_entries: Vec<(usize, f64)> = chart[m][i]
                    .iter().filter(|(_, e)| e.probability > 0.0).map(|(nt_id, e)| (*nt_id, e.probability)).collect();
                let right_span_entries: Vec<(usize, f64)> = chart[j][m]
                    .iter().filter(|(_, e)| e.probability > 0.0).map(|(nt_id, e)| (*nt_id, e.probability)).collect();

                // Try all binary rules A → B C
                for (b_nt_id, b_prob) in &left_span_entries {
                    for (c_nt_id, c_prob) in &right_span_entries {
                        // Lookup binary rules using (B_ID, C_ID)
                        if let Some(rules) = grammar.binary_rules_by_children.get(&(*b_nt_id, *c_nt_id)) {
                            for rule in rules { 
                                let new_prob = rule.probability * b_prob * c_prob;
                                let a_nt_id = rule.lhs_id; // ID of A

                                let current_best_in_cell_updates = cell_updates.entry(a_nt_id).or_insert_with(|| ChartEntry {
                                    probability: 0.0, backpointer: None,
                                });

                                if new_prob > current_best_in_cell_updates.probability {
                                    current_best_in_cell_updates.probability = new_prob;
                                    current_best_in_cell_updates.backpointer = Some(BackPointer::Binary {
                                        split_point: m,
                                        left_child_non_terminal_id: *b_nt_id,
                                        right_child_non_terminal_id: *c_nt_id,
                                    });
                                }
                            }
                        }
                    }
                }
            }

            // iF start symbol derives the whole sentence, build parse tree
            let target_cell = &mut chart[j][i];
            for (nt_id_from_update, entry_from_update) in cell_updates {
                if entry_from_update.probability > 0.0 {
                    let current_target_entry = target_cell.entry(nt_id_from_update).or_insert_with(|| ChartEntry {
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
    if let Some(final_entry) = chart[n][0].get(&start_symbol_id) {
        if final_entry.probability > 0.0 {
            // Reconstruct tree using start symbol ID
            return reconstruct_tree(grammar, &chart, start_symbol_id, 0, n, words);
        }
    }

    format!("(NOPARSE {})", words.join(" "))
}

fn apply_unary_closure(grammar: &Grammar, cell: &mut HashMap<usize, ChartEntry>) {
     let mut changed = true;
     while changed {
        changed = false;
        // Collect updates to avoid changing the map while iterating
        let mut additions: Vec<(usize, ChartEntry)> = Vec::new();

        for (b_nt_id_ref, b_entry) in cell.iter() {
            if b_entry.probability == 0.0 { continue; }
            let b_nt_id = *b_nt_id_ref;

             // Find rules A -> B where B is b_nt_id
             if let Some(unary_rules) = grammar.unary_rules_by_rhs.get(&b_nt_id) {
                 for rule in unary_rules { // rule is unary rule (A_ID -> B_ID)
                     let new_prob = rule.probability * b_entry.probability;
                     let a_nt_id = rule.lhs_id; // ID of A

                     // Check curent probability of A in this cell
                     let current_prob_a = cell.get(&a_nt_id).map_or(0.0, |e| e.probability);

                     // If this path to A is better, prepare an update
                     if new_prob > current_prob_a {
                         let new_entry_a = ChartEntry {
                             probability: new_prob,
                             backpointer: Some(BackPointer::Unary {
                                 child_non_terminal_id: b_nt_id, // Store ID of B
                             }),
                         };
                         additions.push((a_nt_id, new_entry_a)); // Add (A_ID, new_entry_for_A)
                         changed = true;
                     }
                 }
             }
        }
        // Apply colected additions to the cell
        for (nt_id, entry) in additions {
            cell.insert(nt_id, entry);
        }
     }
}

// rekursive reconstruction of the parse tree from the completed CYK chart
fn reconstruct_tree(
    grammar: &Grammar,
    chart: &Chart,
    non_terminal_id: usize,
    i: usize, // span start index 
    j: usize, // span end index 
    words: &[String]
) -> String {
    let non_terminal_str = &grammar.id_to_non_terminal[non_terminal_id];

    let entry = chart[j][i].get(&non_terminal_id) 
                     .unwrap_or_else(|| panic!("reconstruct_tree: NT ID '{}' ({}) not found in chart for span ({},{})", non_terminal_id, non_terminal_str, i, j));

    match entry.backpointer.as_ref().expect("reconstruct_tree: Missing backpointer") {
        BackPointer::Terminal => {
            //  A -> word
             format!("({} {})", non_terminal_str, words[i])
        }
        BackPointer::Unary { child_non_terminal_id } => {
            // A -> B
             let child_tree = reconstruct_tree(grammar, chart, *child_non_terminal_id, i, j, words);
             format!("({} {})", non_terminal_str, child_tree)
        }
        BackPointer::Binary { split_point, left_child_non_terminal_id, right_child_non_terminal_id } => {
            //  A -> B C
             let m = *split_point;
             let left_tree = reconstruct_tree(grammar, chart, *left_child_non_terminal_id, i, m, words);
             let right_tree = reconstruct_tree(grammar, chart, *right_child_non_terminal_id, m, j, words);
             format!("({} {} {})", non_terminal_str, left_tree, right_tree)
        }
    }
}