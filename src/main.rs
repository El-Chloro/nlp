// --- Module Declarations ---
mod structs;
mod parser;
mod rules;
mod output;
mod grammar;
mod cyk;
mod transformations;
#[cfg(test)]
mod tests;

// --- Imports ---
use clap::Parser;
use std::io::{self, BufRead};
use std::collections::HashMap;

use crate::structs::Commands;
use crate::parser::parse_tree;
use crate::rules::extract_rules;
use crate::output::{write_pcfg_output, tree_to_string};
use crate::grammar::load_grammar;
use crate::cyk::parse_sentence;
use crate::transformations::{debinarise_node, collect_leaves, replace_rare_words, restore_words, replace_rare_words_with_signatures, get_signature};


use std::time::Instant;

// --- Main Logic ---
fn main() -> io::Result<()> {
    let total_time = Instant::now();
    let start_time = Instant::now();
    let cli = structs::Cli::parse();

    match cli.command {
        Commands::Induce(args) => {
            let mut non_lexical_rules: HashMap<String, u64> = HashMap::new();
            let mut lexical_rules: HashMap<String, u64> = HashMap::new();

            let stdin = io::stdin();
            let reader = stdin.lock();

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
            // Check for unimplemented optional flags
            if args.threshold_beam.is_some() || args.rank_beam.is_some() || args.astar_outside_weights_file.is_some() {
                eprintln!("Error: A specified option is not implemented.");
                std::process::exit(22);
            }

            if args.unking && args.smoothing {
                eprintln!("Error: --unking and --smoothing flags cannot be used at the same time.");
                std::process::exit(1);
            }

            eprintln!("Loading grammar from: {:?} and {:?}", args.rules_file, args.lexicon_file);

            // Load Grammar
            let grammar = match load_grammar(&args.rules_file, &args.lexicon_file) {
                 Ok(g) => g,
                 Err(e) => {
                     eprintln!("Error loading grammar: {}", e);
                     std::process::exit(2);
                 }
            };
            // eprintln!("Grammar loaded successfully.");

            if args.paradigma.to_lowercase() != "cyk" {
                 eprintln!("Error: Invalid paradigm '{}'. Only 'cyk' is supported.", args.paradigma);
                 std::process::exit(22);
            }

            // Read sentences
            // eprintln!("Reading sentences");
            let stdin = io::stdin();
            let reader = stdin.lock();
            let duration = start_time.elapsed();
            // eprintln!("Program runtime: {:?}", duration);

            for (line_num, line_result) in reader.lines().enumerate() {
                let start_time = Instant::now();
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

                 let mut words: Vec<String> = trimmed_line.split_whitespace().map(String::from).collect();

                 if words.is_empty() {
                    continue;
                 }

                 let original_words = words.clone();

                 // Handle --unking and --smoothing flags for parser
                 if args.unking {
                     for word in &mut words {
                         if !grammar.terminals.contains(word) {
                             *word = "UNK".to_string();
                         }
                     }
                 } else if args.smoothing {
                     for (i, word) in words.iter_mut().enumerate() {
                         if !grammar.terminals.contains(word) {
                             *word = get_signature(word, i);
                         }
                     }
                 }

                 let parse_result = parse_sentence(&grammar, &words, &args.initial_nonterminal);

                 match parse_result {
                     Some(mut tree) => {
                         // Restore original words if unking or smoothing was active
                         if args.unking || args.smoothing {
                            restore_words(&mut tree, &original_words);
                         }
                         println!("{}", tree_to_string(&tree));
                     }
                     None => {
                         println!("(NOPARSE {})", original_words.join(" "));
                     }
                 }

                 let duration = start_time.elapsed();
                //  eprintln!("Sentence runtime: {:?}", duration);
            }
            //  eprintln!("Parsing complete.");
            let duration = total_time.elapsed();
            // eprintln!("Total program runtime: {:?}", duration);
        }
        Commands::Binarise(args) => {
            let stdin = io::stdin();
            for line_result in stdin.lock().lines() {
                let line = line_result?;
                let trimmed_line = line.trim();
                if trimmed_line.is_empty() {
                    continue;
                }
                match parse_tree(trimmed_line) {
                    Ok(tree) => {
                        let binarised_tree = transformations::binarise_tree(&tree, args.horizontal, args.vertical);
                        println!("{}", tree_to_string(&binarised_tree));
                    }
                    Err(e) => eprintln!("Error parsing tree: {:?} on line '{}'", e, trimmed_line),
                }
            }
        }
        Commands::Debinarise(_) => {
            let stdin = io::stdin();
            for line_result in stdin.lock().lines() {
                let line = line_result?;
                let trimmed_line = line.trim();
                if trimmed_line.is_empty() {
                    continue;
                }
                match parse_tree(trimmed_line) {
                    Ok(tree) => {
                        let debinarised_tree = debinarise_node(tree);
                        println!("{}", tree_to_string(&debinarised_tree));
                    }
                    Err(e) => eprintln!("Error parsing tree: {:?} on line '{}'", e, trimmed_line),
                }
            }
        }
        Commands::Unk(args) => {
            let stdin = io::stdin();
            let lines: Vec<String> = stdin.lock().lines().collect::<Result<_, _>>()?;

            let mut word_counts = HashMap::new();
            let mut parsed_trees = Vec::new();

            // First pass: parse all trees and count word frequencies
            for line in &lines {
                let trimmed_line = line.trim();
                if trimmed_line.is_empty() {
                    continue;
                }
                match parse_tree(trimmed_line) {
                    Ok(tree) => {
                        let mut leaves = Vec::new();
                        collect_leaves(&tree, &mut leaves);
                        for leaf in leaves {
                            *word_counts.entry(leaf.label.clone()).or_insert(0) += 1;
                        }
                        parsed_trees.push(tree);
                    }
                    Err(e) => eprintln!("Error parsing tree: {:?} on line '{}'", e, trimmed_line),
                }
            }

            // Second pass: replace rare words and print trees
            for tree in &mut parsed_trees {
                replace_rare_words(tree, &word_counts, args.threshold);
                println!("{}", tree_to_string(tree));
            }
        }
        Commands::Smooth(args) => {
            let stdin = io::stdin();
            let lines: Vec<String> = stdin.lock().lines().collect::<Result<_, _>>()?;

            let mut word_counts = HashMap::new();
            let mut parsed_trees = Vec::new();

            // First pass: parse all trees and count word frequencies
            for line in &lines {
                let trimmed_line = line.trim();
                if trimmed_line.is_empty() {
                    continue;
                }
                match parse_tree(trimmed_line) {
                    Ok(tree) => {
                        let mut leaves = Vec::new();
                        collect_leaves(&tree, &mut leaves);
                        for leaf in leaves {
                            *word_counts.entry(leaf.label.clone()).or_insert(0) += 1;
                        }
                        parsed_trees.push(tree);
                    }
                    Err(e) => eprintln!("Error parsing tree: {:?} on line '{}'", e, trimmed_line),
                }
            }

            // Second pass: replace rare words with signatures and print trees
            for tree in &mut parsed_trees {
                replace_rare_words_with_signatures(tree, &word_counts, args.threshold);
                println!("{}", tree_to_string(tree));
            }
        }
        Commands::Outside(_) => {
            eprintln!("Error: This command is not implemented.");
            std::process::exit(22);
        }
    }

    Ok(())
}