
use clap::Parser;
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Parser, Debug)]
#[command(name = "pcfg_tool", about = "Tools for PCFG-based parsing of natural language sentences", version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::Subcommand, Debug)]
enum Commands {

    Induce(InduceArgs),
}

#[derive(Parser, Debug)]
struct InduceArgs {
    #[arg()] 
    grammar_output_prefix: Option<String>,
}


fn main() -> io::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Induce(args) => {
            let mut grammar_rules: HashMap<String, u64> = HashMap::new();

            let stdin = io::stdin();
            let reader = stdin.lock();

            eprintln!("Reading trees from standard input and inducing PCFG..."); 

            for (line_num, line_result) in reader.lines().enumerate() {
                match line_result {
                    Ok(line) => {
                        let mut current_line_structure = line;
                        if current_line_structure.trim().is_empty() {
                            continue;
                        }

                        loop {
                            if let Some(innermost_slice) = find_innermost_parentheses(&current_line_structure) {
                                let innermost_content = innermost_slice.to_string();
                                let search_pattern = format!("({})", innermost_content);

                                if let Some(replacement_token) = first_word_with_space(&innermost_content) {
                                    let occurrence_count = current_line_structure.matches(&search_pattern).count();

                                    if occurrence_count > 0 {
                                        current_line_structure = current_line_structure.replace(&search_pattern, replacement_token);

                                        let rule_text = innermost_content.replacen(' ', " -> ", 1);

                                        *grammar_rules.entry(rule_text.clone()).or_insert(0) += occurrence_count as u64;
                                    } else {
                                        eprintln!(
                                            "INTERNAL ERROR (Line {}): Could not find '{}' in '{}', although it was detected? Skipping replacement.",
                                            line_num + 1, search_pattern, current_line_structure
                                        );
                                        break;
                                    }
                                } else {
                                     eprintln!(
                                        "WARNING (Line {}): Could not find the first word (LHS) in the innermost content '{}'. Skipping replacement for this part.",
                                        line_num + 1, innermost_content
                                    );
                                     current_line_structure = current_line_structure.replace(&search_pattern, ""); 
                                }
                            } else {

                                if current_line_structure.split_whitespace().count() > 1 || current_line_structure.contains(['(',')']) {
                                     eprintln!(
                                         "WARNING (Line {}): Processing finished, but remaining structure is not a single token: '{}'",
                                         line_num + 1, current_line_structure
                                     );
                                }
                                break; 
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("Error reading line {} from standard input: {}", line_num + 1, e);
                    }
                }
            } 

            // --- Calculate Probabilities ---
            // 1. Calculate the total count for each left-hand side non-terminal (LHS)
            let mut lhs_totals: HashMap<String, u64> = HashMap::new();
            for (rule, count) in &grammar_rules {
                if let Some((lhs, _)) = rule.split_once(" -> ") {
                    *lhs_totals.entry(lhs.trim().to_string()).or_insert(0) += count;
                }
            }

            // --- Write Output ---
            write_pcfg_output(&grammar_rules, &lhs_totals, args.grammar_output_prefix)?;

            eprintln!("PCFG induction complete."); 
        } 
    } 

    Ok(()) 
}

fn write_pcfg_output(
    grammar_rules: &HashMap<String, u64>, lhs_totals: &HashMap<String, u64>, output_prefix: Option<String>, ) -> io::Result<()> {

    let mut all_lhs_non_terminals: HashSet<String> = HashSet::new();
    for rule_string in grammar_rules.keys() {
        if let Some((lhs, _)) = rule_string.split_once(" -> ") {
            all_lhs_non_terminals.insert(lhs.trim().to_string());
        }
    }

    let mut sorted_rules: Vec<_> = grammar_rules.iter().collect();
    // Sort alphabetically by the full rule string ("LHS -> RHS")
    sorted_rules.sort_by_key(|(rule_key, _)| *rule_key);


    if let Some(prefix) = output_prefix {
        // --- Write to Files ---
        eprintln!("Writing PCFG to files with prefix: {}", prefix); 
        let rules_output_filename = format!("{}.rules", prefix);
        let lexicon_output_filename = format!("{}.lexicon", prefix);
        let words_output_filename = format!("{}.words", prefix);

        let rules_output_file = File::create(&rules_output_filename)?;
        let mut rules_writer = BufWriter::new(rules_output_file);

        let lexicon_output_file = File::create(&lexicon_output_filename)?;
        let mut lexicon_writer = BufWriter::new(lexicon_output_file);

        let words_output_file = File::create(&words_output_filename)?;
        let mut words_writer = BufWriter::new(words_output_file);

        let mut unique_words_for_output: HashSet<String> = HashSet::new();

        for (rule, count) in sorted_rules {
            if let Some((lhs, rhs)) = rule.split_once(" -> ") {
                let lhs_trimmed = lhs.trim();
                let rhs_trimmed = rhs.trim();

                if let Some(total_count) = lhs_totals.get(lhs_trimmed) {
                    let relative_frequency = if *total_count > 0 {
                        *count as f64 / *total_count as f64
                    } else {
                         eprintln!(
                            "Warning: Total count for LHS '{}' was zero for rule '{}'. Setting frequency to 0.0.",
                            lhs_trimmed, rule
                         );
                        0.0
                    };

                    let output_line = format!("{} {:.6}", rule, relative_frequency); 

                    let rhs_components: Vec<&str> = rhs_trimmed.split_whitespace().collect();

                    if rhs_components.len() == 1 {
                        let single_rhs_element = rhs_components[0];

                        if all_lhs_non_terminals.contains(single_rhs_element) {
                             // It's a unary grammar rule
                            writeln!(rules_writer, "{}", output_line)?;
                        } else {
                             // It's a lexicon rule (terminal symbol)
                            writeln!(lexicon_writer, "{}", output_line)?;
                            // Add the terminal word to the set for grammar.words
                            if unique_words_for_output.insert(single_rhs_element.to_string()) {
                                writeln!(words_writer, "{}", single_rhs_element)?;
                            }
                        }
                    } else {
                        writeln!(rules_writer, "{}", output_line)?;
                    }
                } else {
                     eprintln!(
                        "Internal error: Could not find total count for LHS '{}' from rule '{}'. Skipping rule.",
                        lhs_trimmed, rule
                     );
                }
            } else {
                 eprintln!(
                    "Warning: Rule format incorrect, skipping output: {}",
                    rule
                 );
            }
        } 

        rules_writer.flush()?;
        lexicon_writer.flush()?;
        words_writer.flush()?;

        eprintln!("Successfully wrote: {}, {}, {}", rules_output_filename, lexicon_output_filename, words_output_filename); 

    } else {
        // --- Write to Standard Output ---
        eprintln!("Writing combined PCFG rules to standard output..."); 
        let stdout = io::stdout();
        let mut writer = BufWriter::new(stdout.lock()); 

        for (rule, count) in sorted_rules {
            if let Some((lhs, rhs)) = rule.split_once(" -> ") {
                let lhs_trimmed = lhs.trim();

                if let Some(total_count) = lhs_totals.get(lhs_trimmed) {
                     let relative_frequency = if *total_count > 0 {
                        *count as f64 / *total_count as f64
                    } else {

                         eprintln!(
                            "Warning: Total count for LHS '{}' was zero for rule '{}'. Setting frequency to 0.0.",
                            lhs_trimmed, rule
                         );
                        0.0
                    };
                     // Format the output line: "LHS -> RHS Frequency"
                    let output_line = format!("{} {:.6}", rule, relative_frequency); 
                    writeln!(writer, "{}", output_line)?; 
                } else {
                     eprintln!( 
                        "Internal error: Could not find total count for LHS '{}' from rule '{}'. Skipping rule output.",
                        lhs_trimmed, rule
                     );
                }
            } else {
                 eprintln!( 
                    "Warning: Rule format incorrect, skipping output: {}",
                    rule
                 );
            }
        }

        writer.flush()?;
        eprintln!("Finished writing to standard output."); 

    } 

    Ok(())
}


// Get the first non-empty word separated by spaces
fn first_word_with_space(s: &str) -> Option<&str> {
    s.split(' ').filter(|word| !word.is_empty()).next()
}


// Find the content slice of the first innermost pair of parentheses
fn find_innermost_parentheses(s: &str) -> Option<&str> {
    let s = s.trim();
    
    let mut max_depth = 0;          
    let mut current_depth = 0;      
    let mut max_depth_start_index = None;
    let mut innermost_start_index = 0; 
    let mut innermost_end_index = 0; 

    // First pass: Find max nesting depth and check balance.
    for (i, c) in s.char_indices() {
        match c {
            '(' => {
                current_depth += 1;
                if current_depth > max_depth {
                    max_depth = current_depth;
                    max_depth_start_index = Some(i); 
                }
            }
            ')' => {
                if current_depth == 0 {
                    return None; 
                }
                current_depth -= 1;
            }
            _ => {}
        }
    }

     if current_depth != 0 {
        return None;
    }

    if max_depth == 0 {
        return None;
    }

    // Handle simple case: only one level of parentheses like "(LHS RHS)".
    if max_depth == 1 && s.starts_with('(') && s.ends_with(')') {
        let inner = &s[1..s.len() - 1];
        return Some(inner.trim());
    }

    


    // Second pass: Find the exact start/end indices of the *first* innermost content.
    current_depth = 0;
    let mut start_content_index : Option<usize> = None;

    for (i, c) in s.char_indices() {
         match c {
            '(' => {
                current_depth += 1;
                if current_depth == max_depth {
                     start_content_index = Some(i + 1); 
                }
            }
            ')' => {
                if current_depth == max_depth && start_content_index.is_some() {
                     return Some(&s[start_content_index.unwrap()..i]); 
                }
                if current_depth > 0 { 
                    current_depth -= 1;
                }

                 if current_depth < max_depth {
                     start_content_index = None;
                 }
            }
            _ => {}
        }
    }
    None // Should not be reached
}


// --- Test Module ---
#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read;
    use tempfile::tempdir; 

    // --- Tests for find_innermost_parentheses ---

    #[test]
    fn find_innermost_simple() {
        assert_eq!(find_innermost_parentheses("(A (B C))"), Some("B C"));
    }

    #[test]
    fn find_innermost_deep() {
        assert_eq!(find_innermost_parentheses("(A (B (C D)))"), Some("C D"));
    }

    #[test]
    fn find_innermost_multiple_at_same_depth() {
        assert_eq!(find_innermost_parentheses("(A (B C) (D E))"), Some("B C"));
    }

    #[test]
    fn find_innermost_adjacent_at_same_depth() {
        assert_eq!(find_innermost_parentheses("((A B) (C D))"), Some("A B"));
    }

    #[test]
    fn find_innermost_no_parentheses() {
        assert_eq!(find_innermost_parentheses("A B C"), None);
    }

    #[test]
    fn find_innermost_empty_string() {
        assert_eq!(find_innermost_parentheses(""), None);
    }

    #[test]
    fn find_innermost_empty_content() {
        assert_eq!(find_innermost_parentheses("()"), Some(""));
        assert_eq!(find_innermost_parentheses("(A ())"), Some(""));
        assert_eq!(find_innermost_parentheses("(())"), Some(""));
    }

    #[test]
    fn find_innermost_outer_only() {
        assert_eq!(find_innermost_parentheses("(A B C)"), Some("A B C"));
    }

    #[test]
    fn find_innermost_with_spaces() {
        assert_eq!(find_innermost_parentheses(" ( A ( B C ) ) "), Some(" B C "));
        assert_eq!(find_innermost_parentheses("( A B )"), Some("A B"));
    }

    #[test]
    fn find_innermost_complex_ptb_example() {
        let complex = "(ROOT (S (NP (DT The) (NN dog)) (VP (VBD chased) (NP (DT a) (NN cat)))))";
        assert_eq!(find_innermost_parentheses(complex), Some("DT a"));
    }

    #[test]
    fn find_innermost_single_word_content() {
        assert_eq!(find_innermost_parentheses("(NN dog)"), Some("NN dog"));
         assert_eq!(find_innermost_parentheses("(word)"), Some("word"));
    }

    #[test]
    fn find_innermost_unbalanced_start() {
        assert_eq!(find_innermost_parentheses("(A (B C"), None);
        assert_eq!(find_innermost_parentheses("((A)"), None);
    }

    #[test]
    fn find_innermost_unbalanced_end() {
        assert_eq!(find_innermost_parentheses("A B C))"), None);
        assert_eq!(find_innermost_parentheses("(A))"), None);
        assert_eq!(find_innermost_parentheses(")("), None); 
    }

    // --- Tests for first_word_with_space ---

    #[test]
    fn first_word_basic() {
        assert_eq!(first_word_with_space("NP VP S"), Some("NP"));
    }

    #[test]
    fn first_word_single() {
        assert_eq!(first_word_with_space("NP"), Some("NP"));
    }

    #[test]
    fn first_word_leading_space() {
        assert_eq!(first_word_with_space("  NP VP"), Some("NP"));
    }

    #[test]
    fn first_word_multiple_internal_spaces() {
        assert_eq!(first_word_with_space("NP  VP   S"), Some("NP"));
    }

    #[test]
    fn first_word_empty() {
        assert_eq!(first_word_with_space(""), None);
    }

    #[test]
    fn first_word_only_spaces() {
        assert_eq!(first_word_with_space("   "), None);
    }

    // --- Tests for write_pcfg_output (adapted from write_grammar_files) ---

    #[test]
    fn write_output_to_files() -> io::Result<()> {
        let dir = tempdir()?;
        let current_dir = std::env::current_dir()?;
        std::env::set_current_dir(dir.path())?;

        let mut grammar_rules: HashMap<String, u64> = HashMap::new();
        grammar_rules.insert("S -> NP VP".to_string(), 10);
        grammar_rules.insert("NP -> DT NN".to_string(), 8);
        grammar_rules.insert("NP -> NNP".to_string(), 2);    
        grammar_rules.insert("VP -> V NP".to_string(), 9);
        grammar_rules.insert("DT -> the".to_string(), 5);    
        grammar_rules.insert("NN -> dog".to_string(), 3);    
        grammar_rules.insert("NN -> cat".to_string(), 3);    
        grammar_rules.insert("V -> chased".to_string(), 9);   
        grammar_rules.insert("NNP -> Peter".to_string(), 2); 

        let mut lhs_totals: HashMap<String, u64> = HashMap::new();
        lhs_totals.insert("S".to_string(), 10);
        lhs_totals.insert("NP".to_string(), 10); // 8 + 2
        lhs_totals.insert("VP".to_string(), 9);
        lhs_totals.insert("DT".to_string(), 5);
        lhs_totals.insert("NN".to_string(), 6); // 3 + 3
        lhs_totals.insert("V".to_string(), 9);
        lhs_totals.insert("NNP".to_string(), 2);

        let output_prefix = "test_grammar".to_string();

        write_pcfg_output(&grammar_rules, &lhs_totals, Some(output_prefix.clone()))?;

        // --- Assertions ---
        let rules_content = fs::read_to_string(format!("{}.rules", output_prefix))?;
        let lexicon_content = fs::read_to_string(format!("{}.lexicon", output_prefix))?;
        let words_content = fs::read_to_string(format!("{}.words", output_prefix))?;


        let expected_rules = [
            "NP -> DT NN 0.800000", // 8 / 10
            "NP -> NNP 0.200000",   // 2 / 10 
            "S -> NP VP 1.000000",   // 10 / 10
            "VP -> V NP 1.000000",   // 9 / 9
        ].join("\n") + "\n"; 

        let expected_lexicon = [
            "DT -> the 1.000000",    // 5 / 5
            "NN -> cat 0.500000",    // 3 / 6
            "NN -> dog 0.500000",    // 3 / 6
            "NNP -> Peter 1.000000", // 2 / 2
            "V -> chased 1.000000",  // 9 / 9
        ].join("\n") + "\n"; 

         let expected_words_vec = vec!["Peter", "cat", "chased", "dog", "the"];
         let mut sorted_expected_words = expected_words_vec.clone();
         sorted_expected_words.sort();
         let expected_words_string = sorted_expected_words.join("\n") + "\n";

         let mut actual_words: Vec<String> = words_content.lines().map(String::from).collect();
         actual_words.sort(); 
         let actual_words_string = actual_words.join("\n") + "\n";

        assert_eq!(rules_content, expected_rules);
        assert_eq!(lexicon_content, expected_lexicon);
        assert_eq!(actual_words_string, expected_words_string);

        // --- Cleanup ---
        std::env::set_current_dir(current_dir)?; 
        dir.close()?; 
        Ok(())
    }

     // Test handling of zero total count for an LHS (should result in 0.0 frequency)
    #[test]
    fn write_output_zero_total_count() -> io::Result<()> {
        let dir = tempdir()?;
        let current_dir = std::env::current_dir()?;
        std::env::set_current_dir(dir.path())?;

        let mut grammar_rules: HashMap<String, u64> = HashMap::new();
        grammar_rules.insert("S -> NP VP".to_string(), 0);

        let mut lhs_totals: HashMap<String, u64> = HashMap::new();
        lhs_totals.insert("S".to_string(), 0); 

         let output_prefix = "zero_test".to_string();
         write_pcfg_output(&grammar_rules, &lhs_totals, Some(output_prefix.clone()))?;

        let rules_content = fs::read_to_string(format!("{}.rules", output_prefix))?;
        let expected_rules = "S -> NP VP 0.000000\n";

        assert_eq!(rules_content, expected_rules);

        assert!(fs::read_to_string(format!("{}.lexicon", output_prefix))?.is_empty());
        assert!(fs::read_to_string(format!("{}.words", output_prefix))?.is_empty());

        std::env::set_current_dir(current_dir)?;
        dir.close()?;
        Ok(())
    }
} // End of the test module