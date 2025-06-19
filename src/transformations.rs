use crate::structs::Node;
use std::collections::HashMap;

/// removes extra nodes from the binarization in the tree
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

/// collects all leaf nodes from the tree (the words).
pub fn collect_leaves<'a>(node: &'a Node, leaves: &mut Vec<&'a Node>) {
    if node.is_terminal() {
        leaves.push(node);
    }
    for child in &node.children {
        collect_leaves(child, leaves);
    }
}

/// changes rare word labels to "UNK" in the tree
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

/// Recursively restores the original words back into the tree's leaf nodes
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

/// Start function to start the word restoration process
pub fn restore_words(tree: &mut Node, original_words: &[String]) {
    let mut word_idx = 0;
    restore_words_recursive(tree, original_words, &mut word_idx);
}