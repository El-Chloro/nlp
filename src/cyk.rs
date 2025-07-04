use crate::grammar::Grammar;
use crate::structs::Node;
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct ChartEntry {
    cost: f64,
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
    },
}

type Chart = Vec<Vec<HashMap<usize, ChartEntry>>>;

/// Applies pruning to a single chart cell based on cost
fn prune_cell(
    cell: &mut HashMap<usize, ChartEntry>,
    threshold_beam: Option<f64>,
    rank_beam: Option<usize>,
) {
    if cell.is_empty() || (threshold_beam.is_none() && rank_beam.is_none()) {
        return;
    }

    // 1: convert to Vec for sorting and filtering
    let mut entries: Vec<(usize, ChartEntry)> = cell.drain().collect();

    // 2:Apply Threshold Beam if specified
    if let Some(theta) = threshold_beam {
        // Threshold is a probability ratio [0.0, 1.0]
        if theta >= 0.0 && theta <= 1.0 {
            let best_cost = entries.iter()
                .map(|(_, entry)| entry.cost)
                .fold(f64::INFINITY, f64::min);
            
            if best_cost.is_finite() {
                // Cost threshold. Prune if cost > best_cost - ln(theta)
                let cost_threshold = if theta == 0.0 {
                    f64::INFINITY // Pruning with theta=0 means keep everything
                } else {
                    best_cost - theta.ln()
                };
                
                entries.retain(|(_, entry)| entry.cost <= cost_threshold);
            }
        }
    }

    // 3: apply Rank Beam if specified
    if let Some(k) = rank_beam {
        if k > 0 && entries.len() > k {
            // Sort by cost (ascending). Using partial_sort would be more efficient,
            // but full sort is simpler and correct.
            entries.sort_unstable_by(|(_, a), (_, b)| a.cost.partial_cmp(&b.cost).unwrap_or(std::cmp::Ordering::Equal));
            entries.truncate(k);
        }
    }

    // 4: Refill the cell from the pruned entries
    *cell = entries.into_iter().collect();
}

pub fn parse_sentence(
    grammar: &Grammar,
    words: &[String],
    start_symbol_str: &str,
    threshold_beam: Option<f64>,
    rank_beam: Option<usize>,
) -> Option<Node> {
    let n = words.len();
    if n == 0 {
        return None;
    }

    // Get ID for start symbol string
    let start_symbol_id = match grammar.non_terminal_to_id.get(start_symbol_str) {
        Some(id) => *id,
        None => {
            // This case is handled by returning None, caller can format the error.
            return None;
        }
    };

    // Initialize empty chart
    let mut chart: Chart = vec![vec![HashMap::new(); n + 1]; n + 1];

    // Fill chart with lexical rules for individual words
    for i in 0..n {
        let word = &words[i];
        let j = i + 1;
        let cell = &mut chart[j][i];

        // Handle unknown words if they made it this far (UNK)
        if let Some(rules) = grammar.lexical_rules_by_rhs.get(word) {
            for rule in rules {
                let entry = cell.entry(rule.lhs_id).or_insert_with(|| ChartEntry {
                    cost: f64::INFINITY,
                    backpointer: None,
                });
                if rule.cost < entry.cost {
                    entry.cost = rule.cost;
                    entry.backpointer = Some(BackPointer::Terminal);
                }
            }
        }

        apply_unary_closure(grammar, cell);
        prune_cell(cell, threshold_beam, rank_beam);
    }

    //  Main CYK loop: fill cells for spans of length > 1
    for r in 2..=n { // r: span length
        for i in 0..=(n - r) { // i: span start
            let j = i + r; // j: span end

            // Collect potential updates for the cell (j, i) to avoid borrow checker issues.
            let mut binary_updates: Vec<(usize, f64, BackPointer)> = Vec::new();

            for m in (i + 1)..j { // m: split point
                let left_span_entries = &chart[m][i];
                let right_span_entries = &chart[j][m];

                // Try all binary rules A -> B C
                for (b_nt_id, b_entry) in left_span_entries.iter() {
                    if b_entry.cost.is_infinite() { continue; }
                    for (c_nt_id, c_entry) in right_span_entries.iter() {
                        if c_entry.cost.is_infinite() { continue; }

                        if let Some(rules) = grammar.binary_rules_by_children.get(&(*b_nt_id, *c_nt_id)) {
                            for rule in rules {
                                let new_cost = rule.cost + b_entry.cost + c_entry.cost;
                                let a_nt_id = rule.lhs_id;
                                let backpointer = BackPointer::Binary {
                                    split_point: m,
                                    left_child_non_terminal_id: *b_nt_id,
                                    right_child_non_terminal_id: *c_nt_id,
                                };
                                binary_updates.push((a_nt_id, new_cost, backpointer));
                            }
                        }
                    }
                }
            }

            // Now, apply the collected updates.
            let target_cell = &mut chart[j][i];
            for (a_nt_id, new_cost, backpointer) in binary_updates {
                let entry = target_cell.entry(a_nt_id).or_insert_with(|| ChartEntry {
                    cost: f64::INFINITY,
                    backpointer: None,
                });

                if new_cost < entry.cost {
                    entry.cost = new_cost;
                    entry.backpointer = Some(backpointer);
                }
            }

            // After the binary rules are processed, apply unary closure on the updated cell.
            apply_unary_closure(grammar, target_cell);
            prune_cell(target_cell, threshold_beam, rank_beam);
        }
    }

    // Check if start symbol exists in highest chart cell
    if let Some(final_entry) = chart[n][0].get(&start_symbol_id) {
        if final_entry.cost < f64::INFINITY {
            // Reconstruct tree using start symbol ID
            let tree = reconstruct_tree(grammar, &chart, start_symbol_id, 0, n, words);
            return Some(tree);
        }
    }

    None
}

fn apply_unary_closure(grammar: &Grammar, cell: &mut HashMap<usize, ChartEntry>) {
    // Collect initial non-terminals in the cell
    let mut worklist: Vec<usize> = cell.keys().copied().collect();
    let mut processed = 0;

    while processed < worklist.len() {
        let b_nt_id = worklist[processed];
        processed += 1;

        let b_entry_cost = if let Some(e) = cell.get(&b_nt_id) {
            e.cost
        } else {
            continue;
        };

        if b_entry_cost.is_infinite() { continue; }

        // Find rules A -> B where B is b_nt_id
        if let Some(unary_rules) = grammar.unary_rules_by_rhs.get(&b_nt_id) {
            for rule in unary_rules {
                let new_cost = rule.cost + b_entry_cost;
                let a_nt_id = rule.lhs_id;

                let current_cost_a = cell.get(&a_nt_id).map_or(f64::INFINITY, |e| e.cost);

                if new_cost < current_cost_a {
                    let new_entry_a = ChartEntry {
                        cost: new_cost,
                        backpointer: Some(BackPointer::Unary {
                            child_non_terminal_id: b_nt_id,
                        }),
                    };
                    // Insert or update the entry for A
                    cell.insert(a_nt_id, new_entry_a);

                    // If A is new or updated, add it to the worklist to be processed
                    if !worklist.contains(&a_nt_id) {
                        worklist.push(a_nt_id);
                    }
                }
            }
        }
    }
}


// recursive reconstruction of the parse tree from the completed CYK chart
fn reconstruct_tree(
    grammar: &Grammar,
    chart: &Chart,
    non_terminal_id: usize,
    i: usize, // span start index
    j: usize, // span end index
    words: &[String]
) -> Node {
    let non_terminal_str = &grammar.id_to_non_terminal[non_terminal_id];

    let entry = chart[j][i].get(&non_terminal_id)
                     .unwrap_or_else(|| panic!("reconstruct_tree: NT ID '{}' ({}) not found in chart for span ({},{})", non_terminal_id, non_terminal_str, i, j));

    match entry.backpointer.as_ref().expect("reconstruct_tree: Missing backpointer") {
        BackPointer::Terminal => {
            // A -> word
            Node {
                label: non_terminal_str.clone(),
                children: vec![Node { label: words[i].clone(), children: vec![] }],
            }
        }
        BackPointer::Unary { child_non_terminal_id } => {
            // A -> B
             let child_tree = reconstruct_tree(grammar, chart, *child_non_terminal_id, i, j, words);
             Node {
                 label: non_terminal_str.clone(),
                 children: vec![child_tree],
             }
        }
        BackPointer::Binary { split_point, left_child_non_terminal_id, right_child_non_terminal_id } => {
            // A -> B C
             let m = *split_point;
             let left_tree = reconstruct_tree(grammar, chart, *left_child_non_terminal_id, i, m, words);
             let right_tree = reconstruct_tree(grammar, chart, *right_child_non_terminal_id, m, j, words);
             Node {
                label: non_terminal_str.clone(),
                children: vec![left_tree, right_tree],
             }
        }
    }
}