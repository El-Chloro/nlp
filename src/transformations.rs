use crate::structs::Node;
use std::collections::HashMap;

/// Removes extra nodes from the binarization in the tree.
pub fn debinarise_node(node: Node) -> Node {
    if node.is_terminal() {
        return node;
    }

    let mut new_children = Vec::new();
    for child in node.children {
        // Recursively debinarise children first
        let debinarised_child = debinarise_node(child);

        // Check if the debinarised child is an intermediate binarization node
        if debinarised_child.label.contains('|') && !debinarised_child.is_terminal() {
            // Move its children up to the current node
            new_children.extend(debinarised_child.children);
        } else {
            // Otherwise, keep the child as is
            new_children.push(debinarised_child);
        }
    }

    Node {
        label: node.label,
        children: new_children,
    }
}

/// Binarizes a tree using vertical and horizontal Markovization.
pub fn binarise_tree(root: &Node, h: usize, v: usize) -> Node {
    markovize_recursive(root, &[], h, v)
}

/// Implements the recursive Markovization function.
/// `ancestors` contains the original labels of the parent nodes.
fn markovize_recursive(node: &Node, ancestors: &[String], h: usize, v: usize) -> Node {
    // If the node is a terminal (a word), it is returned unchanged.
    if node.is_terminal() {
        return node.clone();
    }

    // According to the pseudocode: "if t is preterminal then return t"
    // A pre-terminal has exactly one child, and that child is a terminal.
    let is_preterminal = node.children.len() == 1 && node.children[0].is_terminal();
    if is_preterminal {
        return node.clone();
    }

    // 'add_parents(σ)' (vertical Markovization)
    let mut new_label = node.label.clone();
    if v > 1 && !ancestors.is_empty() {
        let num_ancestors_to_take = (v - 1).min(ancestors.len());
        let parent_labels_part = ancestors.iter()
            .take(num_ancestors_to_take)
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("^");
        new_label = format!("{}^{}", parent_labels_part, new_label);
    }
    
    // For recursive calls, the original label of the current node
    // is prepended to the list of ancestors for the children.
    let mut new_ancestors = vec![node.label.clone()];
    new_ancestors.extend_from_slice(ancestors);
    
    // Case: k ≤ 2. The node is already unary or binary.
    if node.children.len() <= 2 {
        let new_children = node
            .children
            .iter()
            .map(|child| markovize_recursive(child, &new_ancestors, h, v))
            .collect();

        return Node {
            label: new_label,
            children: new_children,
        };
    }
    // Case: k > 2. Binarization is required.
    else {
        let markovized_t1 = markovize_recursive(&node.children[0], &new_ancestors, h, v);

        // Create the label for the new intermediate node: σ' ← originalLabel(σ)|⟨label of t2, …, label of th+1⟩
        let intermediate_label_rhs: Vec<&str> = node.children[1..]
            .iter()
            .take(h)
            .map(|child| child.label.as_str())
            .collect();
        
        let intermediate_label = format!("{}|{}", node.label, intermediate_label_rhs.join(","));
        
        let intermediate_node = Node {
            label: intermediate_label,
            children: node.children[1..].to_vec(),
        };

        // Recursive call for the new intermediate node.
        let markovized_intermediate = markovize_recursive(&intermediate_node, &new_ancestors, h, v);

        // Combine the results.
        return Node {
            label: new_label, // The result of add_parents(σ)
            children: vec![markovized_t1, markovized_intermediate],
        };
    }
}

/// Generates a signature for a given word based on its orthographic features.
pub fn get_signature(word: &str, index: usize) -> String {
    if word.is_empty() {
        return "UNK-S".to_string();
    }

    let mut signature = "UNK".to_string();
    let all_digit = !word.is_empty() && word.chars().all(|c| c.is_ascii_digit());

    if all_digit {
        signature.push_str("-N");
    } else {
        // Not all digits, so apply letter-based and contains-digit logic
        let first_char = word.chars().next().unwrap();
        let has_lower = word.chars().any(|c| c.is_lowercase());
        let has_letter = word.chars().any(|c| c.is_alphabetic());

        let letter_suffix = if first_char.is_uppercase() && !has_lower {
            "-AC" // All letters are uppercase, and it starts with a capital.
        } else if first_char.is_uppercase() && index == 0 {
            "-SC" // Sentence Capitalized
        } else if first_char.is_uppercase() {
            "-C"  // Capitalized
        } else if has_lower {
            "-L"  // Lowercase
        } else if has_letter {
            "-U"  // Unusual (e.g., no lowercase, but doesn't start with a capital, like '1WORD' or 'iPod')
        } else {
            "-S"  // Symbol
        };
        signature.push_str(letter_suffix);

        let has_digit = word.chars().any(|c| c.is_ascii_digit());
        if has_digit {
            signature.push_str("-n");
        }
    }

    // dashSuffix
    if word.contains('-') {
        signature.push_str("-H"); // Hyphen
    }

    // periodSuffix
    if word.contains('.') {
        signature.push_str("-P"); // Period
    }
    
    // commaSuffix (-CO instead of -C to avoid collision with Capitalized)
    if word.contains(',') {
        signature.push_str("-CO"); // Comma
    }
    
    // wordSuffix
    if word.len() > 3 {
        if let Some(last_char) = word.chars().last() {
            if last_char.is_alphanumeric() {
                signature.push_str("-");
                signature.push(last_char.to_ascii_lowercase());
            }
        }
    }
    
    signature
}


/// Helper function for `replace_rare_words_with_signatures`.
fn replace_rare_words_with_signatures_recursive(
    node: &mut Node,
    word_counts: &HashMap<String, u64>,
    threshold: u64,
    leaf_index: &mut usize,
) {
    if node.is_terminal() {
        let is_rare = match word_counts.get(&node.label) {
            Some(count) => *count <= threshold,
            None => true, // Not in map -> count is 0 -> rare
        };

        if is_rare {
            node.label = get_signature(&node.label, *leaf_index);
        }

        *leaf_index += 1;
    }
    for child in &mut node.children {
        replace_rare_words_with_signatures_recursive(child, word_counts, threshold, leaf_index);
    }
}

/// Replaces rare words in a tree with their signatures.
pub fn replace_rare_words_with_signatures(
    tree: &mut Node,
    word_counts: &HashMap<String, u64>,
    threshold: u64,
) {
    let mut leaf_index = 0;
    replace_rare_words_with_signatures_recursive(tree, word_counts, threshold, &mut leaf_index);
}


/// Collects all leaf nodes from the tree (the words).
pub fn collect_leaves<'a>(node: &'a Node, leaves: &mut Vec<&'a Node>) {
    if node.is_terminal() {
        leaves.push(node);
    }
    for child in &node.children {
        collect_leaves(child, leaves);
    }
}

/// Changes rare word labels to "UNK" in the tree.
pub fn replace_rare_words(node: &mut Node, word_counts: &HashMap<String, u64>, threshold: u64) {
    if node.is_terminal() {
        if let Some(count) = word_counts.get(&node.label) {
            if *count <= threshold {
                node.label = "UNK".to_string();
            }
        }
    }
    for child in &mut node.children {
        replace_rare_words(child, word_counts, threshold);
    }
}

/// Recursively restores the original words back into the tree's leaf nodes.
fn restore_words_recursive(node: &mut Node, original_words: &[String], word_idx: &mut usize) {
    if *word_idx >= original_words.len() {
        // This should not happen if the tree is correct
        return;
    }
    if node.is_terminal() {
        node.label = original_words[*word_idx].clone();
        *word_idx += 1;
    }
    for child in &mut node.children {
        restore_words_recursive(child, original_words, word_idx);
    }
}

/// Start function to start the word restoration process.
pub fn restore_words(tree: &mut Node, original_words: &[String]) {
    let mut word_idx = 0;
    restore_words_recursive(tree, original_words, &mut word_idx);
}