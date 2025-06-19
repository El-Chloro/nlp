use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;
use std::num::ParseFloatError;

// --- Grammar Structures ---

#[derive(Debug, Clone)]
pub struct LexicalRule {
    pub lhs_id: usize,
    pub rhs: String,
    pub cost: f64,
}

#[derive(Debug, Clone)]
pub struct UnaryRule {
    pub lhs_id: usize,
    pub rhs_id: usize,
    pub cost: f64,
}

#[derive(Debug, Clone)]
pub struct BinaryRule {
    pub lhs_id: usize,
    pub rhs1_id: usize,
    pub rhs2_id: usize,
    pub cost: f64,
}

#[derive(Debug, Clone)]
pub struct Grammar {
    pub non_terminals: HashSet<String>,
    pub terminals: HashSet<String>,
    pub start_symbol: String,

    pub non_terminal_to_id: HashMap<String, usize>,
    pub id_to_non_terminal: Vec<String>,
    next_nt_id: usize,

    pub lexical_rules_by_rhs: HashMap<String, Vec<LexicalRule>>,
    pub unary_rules_by_rhs: HashMap<usize, Vec<UnaryRule>>,
    pub binary_rules_by_children: HashMap<(usize, usize), Vec<BinaryRule>>,
    pub unary_rules_by_lhs: HashMap<usize, Vec<UnaryRule>>,
}

impl Grammar {
    pub fn new() -> Self {
        Grammar {
            non_terminals: HashSet::new(),
            terminals: HashSet::new(),
            start_symbol: String::new(),
            non_terminal_to_id: HashMap::new(),
            id_to_non_terminal: Vec::new(),
            next_nt_id: 0,
            lexical_rules_by_rhs: HashMap::new(),
            unary_rules_by_rhs: HashMap::new(),
            binary_rules_by_children: HashMap::new(),
            unary_rules_by_lhs: HashMap::new(),
        }
    }

    // Get iD for a non-terminal string, if not exist create a new ID
    pub fn get_or_intern_non_terminal(&mut self, nt_name: &str) -> usize {
        if let Some(id) = self.non_terminal_to_id.get(nt_name) {
            *id
        } else {
            let id = self.next_nt_id;
            self.non_terminal_to_id.insert(nt_name.to_string(), id);
            self.id_to_non_terminal.push(nt_name.to_string());
            self.non_terminals.insert(nt_name.to_string());
            self.next_nt_id += 1;
            id
        }
    }

    // --- Test Helper Methods ---
    #[cfg(test)]
    pub fn add_lexical_rule(&mut self, rule: LexicalRule) {
        self.terminals.insert(rule.rhs.clone());
        self.lexical_rules_by_rhs.entry(rule.rhs.clone()).or_default().push(rule);
    }

    #[cfg(test)]
    pub fn add_unary_rule(&mut self, rule: UnaryRule) {
        self.unary_rules_by_rhs.entry(rule.rhs_id).or_default().push(rule.clone());
        self.unary_rules_by_lhs.entry(rule.lhs_id).or_default().push(rule);
    }

    #[cfg(test)]
    pub fn add_binary_rule(&mut self, rule: BinaryRule) {
        self.binary_rules_by_children.entry((rule.rhs1_id, rule.rhs2_id)).or_default().push(rule);
    }
}

// --- Loading Gramar ---

pub fn load_grammar(rules_path: &Path, lexicon_path: &Path) -> io::Result<Grammar> {
    let mut grammar = Grammar::new();

    // --- Load Lexicon File ---
    let lexicon_file = File::open(lexicon_path)?;
    let lexicon_reader = BufReader::new(lexicon_file);
    for (line_num, line_result) in lexicon_reader.lines().enumerate() {
        let line = line_result?;
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() == 3 {
            let lhs_str = parts[0];
            let rhs_word = parts[1].to_string();
            let probability = parse_probability(parts[2], lexicon_path, line_num + 1)?;
            let cost = if probability > 0.0 { -probability.ln() } else { f64::INFINITY };

            let lhs_id = grammar.get_or_intern_non_terminal(lhs_str);
            grammar.terminals.insert(rhs_word.clone());

            let rule = LexicalRule { lhs_id, rhs: rhs_word.clone(), cost };
            grammar.lexical_rules_by_rhs.entry(rhs_word).or_default().push(rule);
        } else if !parts.is_empty() {
            eprintln!("Warning: Skip wrong lexicon line {}: '{}'", line_num + 1, line.trim());
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
             let cost = if probability > 0.0 { -probability.ln() } else { f64::INFINITY };

             if let Some((lhs_str_raw, rhs_part)) = rule_part.split_once(" -> ") {
                 let lhs_str = lhs_str_raw.trim();
                 let rhs_symbols_str: Vec<String> = rhs_part.split_whitespace().map(String::from).collect();

                 let lhs_id = grammar.get_or_intern_non_terminal(lhs_str);

                 match rhs_symbols_str.len() {
                     1 => { // Unary Rule: A -> B
                         let rhs_b_str = &rhs_symbols_str[0];
                         let rhs_b_id = grammar.get_or_intern_non_terminal(rhs_b_str);
                         let rule = UnaryRule { lhs_id, rhs_id: rhs_b_id, cost };
                         grammar.unary_rules_by_rhs.entry(rhs_b_id).or_default().push(rule.clone());
                         grammar.unary_rules_by_lhs.entry(lhs_id).or_default().push(rule);
                     }
                     2 => { // Binary Rule: A -> B C
                         let rhs_b_str = &rhs_symbols_str[0];
                         let rhs_c_str = &rhs_symbols_str[1];
                         let rhs_b_id = grammar.get_or_intern_non_terminal(rhs_b_str);
                         let rhs_c_id = grammar.get_or_intern_non_terminal(rhs_c_str);
                         let rule = BinaryRule { lhs_id, rhs1_id: rhs_b_id, rhs2_id: rhs_c_id, cost };
                         grammar.binary_rules_by_children.entry((rhs_b_id, rhs_c_id)).or_default().push(rule.clone());
                     }
                     _ => { // Not CNF or unary
                        eprintln!("Warning: Skip non-CNF rule line {}: '{}', lhs: {}, rhs: {}", line_num + 1, line.trim(), lhs_str, rhs_part);
                     }
                 }
             } else {
                eprintln!("Warning: Skip wrong rule line {} (no '->'): '{}'", line_num + 1, line.trim());
             }
        } else if !line.trim().is_empty() {
            eprintln!("Warning: Skip wrong rule line {} (no probability): '{}'", line_num + 1, line.trim());
        }
     }

    // --- Determine Start Symbol ---
    if grammar.non_terminals.contains("ROOT") {
        grammar.start_symbol = "ROOT".to_string();
    } else if !grammar.non_terminals.is_empty() {
        if let Some(first_nt_str) = grammar.non_terminals.iter().min() {
            grammar.start_symbol = first_nt_str.clone();
            eprintln!("Warning: 'ROOT' not found, defaulting start symbol to '{}'", first_nt_str);
        } else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "Cannot determine start symbol"));
        }
    } else {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "No non-terminals found in grammar - can not detremine start symbol."));
    }

    // Final check for determine start symbol's existence
    if !grammar.non_terminals.contains(&grammar.start_symbol) {
        let error_msg = format!("Determine start symbol '{}' is not in the set of known non-terminals", grammar.start_symbol);
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