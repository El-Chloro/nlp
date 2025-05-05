// --- Module Deklarationen ---
mod structs;
mod parser;
mod rules;
mod output;
#[cfg(test)]
mod tests; 

// --- Imports ---
use clap::Parser;
use std::io::{self, BufRead};
use std::collections::HashMap;

use crate::structs::{Cli, Commands, Node};
use crate::parser::parse_tree;
use crate::rules::extract_rules;
use crate::output::write_pcfg_output;


// --- Main Logic ---
fn main() -> io::Result<()> {
    let cli = structs::Cli::parse(); 

    match cli.command {
        structs::Commands::Induce(args) => { 
            let mut non_lexical_rules: HashMap<String, u64> = HashMap::new();
            let mut lexical_rules: HashMap<String, u64> = HashMap::new();

            let stdin = io::stdin();
            let reader = stdin.lock();

            eprintln!("Reading trees from standard input and inducing PCFG...");

            for (line_num, line_result) in reader.lines().enumerate() {
                match line_result {
                    Ok(line) => {
                        let trimmed_line = line.trim();
                        if trimmed_line.is_empty() {
                            continue;
                        }

                        match parse_tree(trimmed_line) { 
                            Ok(tree) => {
                                extract_rules(&tree, &mut non_lexical_rules, &mut lexical_rules); 
                            }
                            Err(e) => {
                                eprintln!(
                                    "Error parsing line {}: {:?} - Line: '{}'",
                                    line_num + 1, e, trimmed_line
                                );
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!(
                            "Error reading line {} from standard input: {}",
                            line_num + 1, e
                        );
                    }
                }
            }

            // --- Calculate Probabilities ---
            let mut lhs_totals: HashMap<String, u64> = HashMap::new();
            for (rule, count) in non_lexical_rules.iter().chain(lexical_rules.iter()) {
                 if let Some((lhs, _)) = rule.split_once(" -> ") {
                     *lhs_totals.entry(lhs.trim().to_string()).or_insert(0) += count;
                 } else {
                     eprintln!("Warning: Malformed rule found during LHS total calculation: {}", rule);
                 }
            }

            write_pcfg_output(&non_lexical_rules, &lexical_rules, &lhs_totals, args.grammar_output_prefix)?;

            eprintln!("PCFG induction complete.");
        }
    }

    Ok(())
}