use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::Path;
use std::collections::HashMap;
use std::collections::HashSet;

fn main() -> io::Result<()> {
    let filename = "material/large/training.mrg"; 
    let path = Path::new(filename);
    let mut grammar_rules: HashMap<String, u64> = HashMap::new();

    if !path.exists() {
        eprintln!("Error: File '{}' not found.", filename);
        return Ok(());
    }

    // println!("Reading and processing file: {}", filename);

    let file = File::open(path)?;
    let reader = BufReader::new(file);

    for (line_num, line_result) in reader.lines().enumerate() {
        match line_result {
            Ok(line) => {
                let mut line_structure = line; 
                if line_structure.trim().is_empty() {
                    continue;
                }

                // println!("\nProcessing line {}: {}", line_num + 1, line_structure);

                loop {
                    if let Some(innermost_slice) = find_innermost_parentheses(&line_structure) {
                        let innermost_content = innermost_slice.to_string(); 
                        // println!("  Found innermost parentheses content: '{}'", innermost_content);

                        let search_pattern = format!("({})", innermost_content);

                        if let Some(replacement_token) = first_word_with_space(&innermost_content) {

                            let occurrence_count = line_structure.matches(&search_pattern).count();

                            if occurrence_count > 0 {

                                line_structure = line_structure.replace(&search_pattern, replacement_token);
                                // println!("    -> Replace '{}' with '{}' ({}x)", search_pattern, replacement_token, occurrence_count);
                                // println!("       New text: {}", line_structure);

                                let rule_text = innermost_content.replacen(' ', " -> ", 1);

                                *grammar_rules.entry(rule_text.clone()).or_insert(0) += occurrence_count as u64;

                            } else {
                                eprintln!("INTERNAL ERROR (Line {}): Could not find '{}' in '{}', although it was detected?", line_num + 1, search_pattern, line_structure);
                                break;
                            }
                        } else {
                            eprintln!("WARNING (Line {}): Could not find the first word in the innermost parentheses content '{}'. Aborting processing for this bracket.", line_num + 1, innermost_content);
                            break;
                        }
                    } else {
                        // No more innermost parentheses found, processing of this line finished.
                        // println!("  Processing of line {} finished.", line_num + 1);
                        if line_structure.split_whitespace().count() > 1 || line_structure.contains(['(',')']) {
                            // println!("     -> Remaining structure: {}", line_structure);
                        }
                        break; 
                    }
                }

            }
            Err(e) => {
                eprintln!("Error reading line {} from '{}': {}", line_num + 1, filename, e);
            }
        }
    }

    // 1. Calculate the total count for each left-hand side non-terminal (LHS)
    let mut lhs_totals: HashMap<String, u64> = HashMap::new();
    for (rule, count) in &grammar_rules {
        if let Some((lhs, _)) = rule.split_once(" -> ") {
            *lhs_totals.entry(lhs.to_string()).or_insert(0) += count;
        }
    }

    write_grammar_files(&grammar_rules, &lhs_totals)?;
    Ok(())
}

fn write_grammar_files(
    grammar_rules: &HashMap<String, u64>,
    lhs_totals: &HashMap<String, u64>,
) -> io::Result<()> {
    let mut all_lhs_strings: HashSet<&str> = HashSet::new();
    for rule_string in grammar_rules.keys() {
        if let Some((lhs, _)) = rule_string.split_once(" -> ") {
            all_lhs_strings.insert(lhs.trim()); 
        }
    }

    // --- Sorting Step ---
    let mut sorted_rules: Vec<_> = grammar_rules.iter().collect();

    sorted_rules.sort_by_key(|(rule_key, _)| *rule_key);

    // --- File Setup Step ---
    let rules_output_filename = "grammar.rules";
    let lexicon_output_filename = "grammar.lexicon";
    let words_output_filename = "grammar.words";

    let rules_output_file = File::create(rules_output_filename)?;
    let mut rules_writer = BufWriter::new(rules_output_file);

    let lexicon_output_file = File::create(lexicon_output_filename)?;
    let mut lexicon_writer = BufWriter::new(lexicon_output_file);

    let words_output_file = File::create(words_output_filename)?;
    let mut words_writer = BufWriter::new(words_output_file);

    let mut unique_words_for_output: HashSet<String> = HashSet::new();

    // --- Processing and Writing Loop ---
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

                let output_line = format!("{} {}", rule, relative_frequency);

                // --- Decision Logic: grammar.rules vs grammar.lexicon ---
                let rhs_components: Vec<&str> = rhs_trimmed.split_whitespace().collect();

                if rhs_components.len() == 1 {
                    let single_rhs_element = rhs_components[0];

                    if all_lhs_strings.contains(single_rhs_element) {
                        writeln!(rules_writer, "{}", output_line)?;
                    } else {
                        writeln!(lexicon_writer, "{}", output_line)?;
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

    Ok(())
}

fn first_word_with_space(s: &str) -> Option<&str> {
    s.split(' ').filter(|word| !word.is_empty()).next()
}

fn find_innermost_parentheses(s: &str) -> Option<&str> {
    let mut max_depth = 0; 
    let mut current_depth = 0; 

    // First pass: Find the maximum depth
    for c in s.chars() {
        match c {
            '(' => {
                current_depth += 1; 
                max_depth = max_depth.max(current_depth);
            }
            ')' => {
                current_depth -= 1; 
            }
            _ => {}
        }
    }

     // Handle edge case where string might just be "(...)"
    if max_depth <= 1 {
        if !s.trim().starts_with('(') || !s.trim().ends_with(')') {
           return None; // Not a simple parenthesized expression if depth is <=1
        }
        // If it *is* just "(...)" max_depth will be 1, proceed normally
    }
    if max_depth == 0 { 
        return None; // No parentheses found
    }

    // Second pass: Find the first parenthesis at the maximum depth
    current_depth = 0; 
    let mut start_index = None;

    for (i, c) in s.char_indices() {
        match c {
            '(' => {
                current_depth += 1; 
                // Check if we just entered the maximum depth level
                if current_depth == max_depth { 
                    start_index = Some(i + 1); // Mark start of content *after* '('
                }
            }
            ')' => {
                // Check if we are currently at the maximum depth *and* have a start index
                if current_depth == max_depth && start_index.is_some() { 
                    // Found the end of an innermost parenthesis pair
                    return Some(&s[start_index.unwrap()..i]); // Return the slice between '(' and ')'
                }
                 current_depth -= 1; 
                 // If we dropped below max depth, reset start_index
                if current_depth < max_depth { 
                    start_index = None;
                }
            }
            _ => {}
        }
    }
    None
}


// Example processing comments (kept original examples):
// (ROOT (FRAG (RB Not) (NP-TMP (DT this) (NN year)) (. .)))
// Process:
// 1. Innermost: (DT this) -> replace with DT, rule: DT -> this, count: 1
//    -> (ROOT (FRAG (RB Not) (NP-TMP DT (NN year)) (. .)))
// 2. Innermost: (NN year) -> replace with NN, rule: NN -> year, count: 1
//    -> (ROOT (FRAG (RB Not) (NP-TMP DT NN) (. .)))
// 3. Innermost: (NP-TMP DT NN) -> replace with NP-TMP, rule: NP-TMP -> DT NN, count: 1
//    -> (ROOT (FRAG (RB Not) NP-TMP (. .)))
// 4. Innermost: (RB Not) -> replace with RB, rule: RB -> Not, count: 1
//    -> (ROOT (FRAG RB NP-TMP (. .)))
// 5. Innermost: (. .) -> replace with ., rule: . -> ., count: 1
//    -> (ROOT (FRAG RB NP-TMP .))
// 6. Innermost: (FRAG RB NP-TMP .) -> replace with FRAG, rule: FRAG -> RB NP-TMP ., count: 1
//    -> (ROOT FRAG)
// 7. Innermost: (ROOT FRAG) -> replace with ROOT, rule: ROOT -> FRAG, count: 1
//    -> ROOT

// (ROOT (NP Hello) (NN (DT to) (NP world)))
// Process:
// 1. Innermost: (DT to) -> replace with DT, rule: DT -> to, count: 1
//    -> (ROOT (NP Hello) (NN DT (NP world)))
// 2. Innermost: (NP world) -> replace with NP, rule: NP -> world, count: 1
//    -> (ROOT (NP Hello) (NN DT NP))
// 3. Innermost: (NP Hello) -> replace with NP, rule: NP -> Hello, count: 1
//    -> (ROOT NP (NN DT NP))  <- PROBLEM HERE: Multiple top-level nodes after replacement
// 4. Innermost: (NN DT NP) -> replace with NN, rule: NN -> DT NP, count: 1
//    -> (ROOT NP NN)
// 5. Innermost: (ROOT NP NN) -> replace with ROOT, rule: ROOT -> NP NN, count: 1
//    -> ROOT
//
// Final Rules (from second example with simplified logic):
// "DT -> to": 1
// "NP -> world": 1
// "NP -> Hello": 1
// "NN -> DT NP": 1
// "ROOT -> NP NN": 1 // Note: The original German comments were slightly different for this example output.