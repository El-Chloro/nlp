use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;
use std::num::ParseFloatError;

// --- Grammar Structures ---

#[derive(Debug, Clone)]
pub struct LexicalRule {
    pub lhs: String,
    pub rhs: String, 
    pub probability: f64,
}

#[derive(Debug, Clone)]
pub struct UnaryRule {
    pub lhs: String,
    pub rhs: String, 
    pub probability: f64,
}

#[derive(Debug, Clone)]
pub struct BinaryRule {
    pub lhs: String,
    pub rhs1: String, 
    pub rhs2: String, 
    pub probability: f64,
}

#[derive(Debug, Clone)]
pub struct Grammar {
    pub non_terminals: HashSet<String>,
    pub terminals: HashSet<String>,
    pub start_symbol: String,

    pub lexical_rules_by_rhs: HashMap<String, Vec<LexicalRule>>,
    pub unary_rules_by_rhs: HashMap<String, Vec<UnaryRule>>,
    pub binary_rules_by_children: HashMap<(String, String), Vec<BinaryRule>>,
    pub unary_rules_by_lhs: HashMap<String, Vec<UnaryRule>>,
}

impl Grammar {
    fn add_non_terminal(&mut self, nt: &str) {
        self.non_terminals.insert(nt.to_string());
    }
}


// --- Loading Gramar ---

pub fn load_grammar(rules_path: &Path, lexicon_path: &Path) -> io::Result<Grammar> {
    let mut grammar = Grammar {
        non_terminals: HashSet::new(),
        terminals: HashSet::new(),
        start_symbol: String::new(), 
        lexical_rules_by_rhs: HashMap::new(),
        unary_rules_by_rhs: HashMap::new(),
        binary_rules_by_children: HashMap::new(),
        unary_rules_by_lhs: HashMap::new(),
    };

    // --- Load Lexicon File ---
    let lexicon_file = File::open(lexicon_path)?;
    let lexicon_reader = BufReader::new(lexicon_file);
    for (line_num, line_result) in lexicon_reader.lines().enumerate() {
        let line = line_result?;
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() == 3 {
            let lhs = parts[0].to_string();
            let rhs = parts[1].to_string();
            let probability = parse_probability(parts[2], lexicon_path, line_num + 1)?;

            grammar.add_non_terminal(&lhs);
            grammar.terminals.insert(rhs.clone());

            let rule = LexicalRule { lhs: lhs.clone(), rhs: rhs.clone(), probability };
            grammar.lexical_rules_by_rhs.entry(rhs).or_default().push(rule);
        } else if !parts.is_empty() {
            eprintln!("Warning: Skipping malformed lexicon line {}: '{}'", line_num + 1, line.trim());
        }
    }

    // --- Load File with Rules ---
    let rules_file = File::open(rules_path)?;
    let rules_reader = BufReader::new(rules_file);
     for (line_num, line_result) in rules_reader.lines().enumerate() {
        let line = line_result?;
        if let Some(last_space_idx) = line.rfind(' ') {
             let (rule_part, prob_str) = line.split_at(last_space_idx);
             let probability = parse_probability(prob_str.trim(), rules_path, line_num + 1)?;

             if let Some((lhs_str, rhs_part)) = rule_part.split_once("->") {
                 let lhs = lhs_str.trim().to_string();
                 let rhs_symbols: Vec<String> = rhs_part.split_whitespace().map(String::from).collect();

                 grammar.add_non_terminal(&lhs);

                 match rhs_symbols.len() {
                     1 => {// Unary Rule: A -> B
                         let rhs = rhs_symbols[0].clone();
                         grammar.add_non_terminal(&rhs);
                         let rule = UnaryRule { lhs: lhs.clone(), rhs: rhs.clone(), probability };
                         grammar.unary_rules_by_rhs.entry(rhs.clone()).or_default().push(rule.clone());
                         grammar.unary_rules_by_lhs.entry(lhs).or_default().push(rule);
                     }
                     2 => {// Binary Rule: A -> B C
                         let rhs1 = rhs_symbols[0].clone();
                         let rhs2 = rhs_symbols[1].clone();
                         grammar.add_non_terminal(&rhs1);
                         grammar.add_non_terminal(&rhs2);
                         let rule = BinaryRule { lhs: lhs.clone(), rhs1: rhs1.clone(), rhs2: rhs2.clone(), probability };
                         grammar.binary_rules_by_children.entry((rhs1, rhs2)).or_default().push(rule.clone());
                     }
                     _ => {// Not CNF or unary
                        eprintln!("Warning: Skipping non-CNF rule line {}: '{}'", line_num + 1, line.trim());
                     }
                 }
             } else {
                eprintln!("Warning: Skipping wrong rule line {} (no '->'): '{}'", line_num + 1, line.trim());
             }
        } else if !line.trim().is_empty() {
            eprintln!("Warning: Skipping wrong rule line {} (no probability): '{}'", line_num + 1, line.trim());
        }
     }

    // --- Determine Start Symbol ---
    if grammar.non_terminals.contains("ROOT") {
        grammar.start_symbol = "ROOT".to_string();
    } else if !grammar.non_terminals.is_empty() {
        if let Some(first_nt) = grammar.non_terminals.iter().min() { 
            grammar.start_symbol = first_nt.clone();
            eprintln!("Warning: 'ROOT' not found, defaulting start symbol to '{}'", first_nt);
        } else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "Cannot determine start symbol."));
        }
    } else {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "No non-terminals found in grammar."));
    }

    if !grammar.non_terminals.contains(&grammar.start_symbol) {
        let error_msg = format!("Start symbol '{}' not found in non-terminals.", grammar.start_symbol);
        eprintln!("Error: {}", error_msg);
        return Err(io::Error::new(io::ErrorKind::InvalidData, error_msg));
    }

    Ok(grammar)
}

fn parse_probability(prob_str: &str, file_path: &Path, line_num: usize) -> io::Result<f64> {
    prob_str.parse::<f64>().map_err(|e: ParseFloatError| {
        let msg = format!(
            "Error parsing probability '{}' on line {} in {:?}: {}",
            prob_str, line_num, file_path, e
        );
        io::Error::new(io::ErrorKind::InvalidData, msg)
    })
}
