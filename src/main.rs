use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::Path;
use std::collections::HashMap;

fn main() -> io::Result<()> {
    let filename = "material/large/training.mrg"; 
    let path = Path::new(filename);
    let mut grammar_rules: HashMap<String, i32> = HashMap::new();

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

                                *grammar_rules.entry(rule_text.clone()).or_insert(0) += occurrence_count as i32;

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

    // println!("All lines processed. Writing grammar rules...");

    let mut sorted_rules: Vec<_> = grammar_rules.iter().collect();

    // Sort by key (the rule string)
    sorted_rules.sort_by_key(|(k, _)| *k);

    let output_filename = "grammar.rules"; 
    let output_file = File::create(output_filename)?;
    let mut writer = BufWriter::new(output_file);

    for (rule, count) in sorted_rules {
        writeln!(writer, "{} {}", rule, count)?;
    }

    writer.flush()?;

    // println!("Grammar rules successfully written to '{}'.", output_filename);

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