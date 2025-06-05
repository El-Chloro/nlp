// --- Module Deklarationen ---
mod structs;
mod parser;
mod rules;
mod output;
mod grammar; 
mod cyk;
#[cfg(test)]
mod tests; 

// --- Imports ---
use clap::Parser;
use std::io::{self, BufRead};
use std::collections::HashMap;

use crate::structs::Commands;
use crate::parser::parse_tree;
use crate::rules::extract_rules;
use crate::output::write_pcfg_output;
use crate::grammar::load_grammar;
use crate::cyk::parse_sentence;


use std::time::Instant; ////////////////////////////////////////////////////////////////////////////////////////////////////

// --- Main Logic ---
fn main() -> io::Result<()> {
    let total_time = Instant::now(); ////////////////////////////////////////////////////////////////////////////////////////////////////
     let start_time = Instant::now(); ////////////////////////////////////////////////////////////////////////////////////////////////////
    let cli = structs::Cli::parse(); 

    match cli.command {
        Commands::Induce(args) => { 
            let mut non_lexical_rules: HashMap<String, u64> = HashMap::new();
            let mut lexical_rules: HashMap<String, u64> = HashMap::new();

            let stdin = io::stdin();
            let reader = stdin.lock();

            // eprintln!("Reading trees from standard input and inducing PCFG...");

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
                     eprintln!("Warning: wrong rule found during LHS total calculation: {}", rule);
                 }
            }

            write_pcfg_output(&non_lexical_rules, &lexical_rules, &lhs_totals, args.grammar_output_prefix)?;

            eprintln!("PCFG induction complete.");
        }
        Commands::Parse(args) => {
            eprintln!("Loading grammar from: {:?} and {:?}", args.rules_file, args.lexicon_file);

            // Load Grammar
            let grammar = match load_grammar(&args.rules_file, &args.lexicon_file) {
                 Ok(g) => g,
                 Err(e) => {
                     eprintln!("Error loading grammar: {}", e);
                     std::process::exit(2);
                 }
            };
            eprintln!("Grammar loaded successfully.");

            if args.paradigma.to_lowercase() != "cyk" {
                 eprintln!("Error: Invalid paradigm '{}'. Only 'cyk' is supported.", args.paradigma);
                 std::process::exit(22);
            }

            // Read sentences
            eprintln!("Reading sentences");
            let stdin = io::stdin();
            let reader = stdin.lock();
            let duration = start_time.elapsed();////////////////////////////////////////////////////////////////////////////////////////////////////
            eprintln!("Programm-Laufzeit: {:?}", duration); ////////////////////////////////////////////////////////////////////////////////////////////////////

            for (line_num, line_result) in reader.lines().enumerate() {
                let start_time = Instant::now(); ////////////////////////////////////////////////////////////////////////////////////////////////////
                 let line = match line_result {
                     Ok(l) => l,
                     Err(e) => {
                         eprintln!("Error reading line {} from standard input: {}", line_num + 1, e);
                         continue;
                     }
                 };

                 let trimmed_line = line.trim();
                 if trimmed_line.is_empty() {
                     continue;
                 }

                 let words: Vec<String> = trimmed_line.split_whitespace().map(String::from).collect();

                 if words.is_empty() {
                    continue;
                 }

                 // Parsing using CYK 
                 // The `initial_nonterminal` is still passed as a String. 
                 // `parse_sentence` will handle its conversion to an ID.
                 let parse_result = parse_sentence(&grammar, &words, &args.initial_nonterminal); //

                 //  Print result
                 println!("{}", parse_result);
                 let duration = start_time.elapsed(); ////////////////////////////////////////////////////////////////////////////////////////////////////
                 eprintln!("Satz-Laufzeit: {:?}", duration); ////////////////////////////////////////////////////////////////////////////////////////////////////

            }
             eprintln!("Parsing complete.");
            let duration = total_time.elapsed(); ////////////////////////////////////////////////////////////////////////////////////////////////////
            eprintln!("Programm-Laufzeit: {:?}", duration); ////////////////////////////////////////////////////////////////////////////////////////////////////
        }
    }

    Ok(())
}