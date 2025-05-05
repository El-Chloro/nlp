use std::collections::HashMap;
use crate::structs::Node; 

// --- Rule Extraction---

pub fn extract_rules(
    node: &Node,
    non_lexical_rules: &mut HashMap<String, u64>,
    lexical_rules: &mut HashMap<String, u64>,
) {
    if node.is_terminal() { 
        return;
    }
    if node.children.len() == 1 && node.children[0].is_terminal() {
        let lhs = node.label.clone();
        let rhs = node.children[0].label.clone();
        let rule = format!("{} -> {}", lhs, rhs);
        *lexical_rules.entry(rule).or_insert(0) += 1;
    }
    else if !node.children.is_empty() {
        let lhs = node.label.clone();
        let rhs_parts: Vec<String> = node.children.iter().map(|c| c.label.clone()).collect();
        let rule = format!("{} -> {}", lhs, rhs_parts.join(" "));
        *non_lexical_rules.entry(rule).or_insert(0) += 1;
        for child in &node.children {
             if !child.is_terminal() {
                extract_rules(child, non_lexical_rules, lexical_rules);
             }
        }
    }
}