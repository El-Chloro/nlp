use std::fs::File; 
use std::io::{self, BufWriter, Write}; 
use std::collections::{HashMap, HashSet}; 

// --- Output Writing---
pub fn write_pcfg_output(
    non_lexical_rules: &HashMap<String, u64>,
    lexical_rules: &HashMap<String, u64>,
    lhs_totals: &HashMap<String, u64>,
    output_prefix: Option<String>,
) -> io::Result<()> {

    let mut combined_rules_for_stdout: Vec<(String, u64)> = Vec::new();
    if output_prefix.is_none() {
        combined_rules_for_stdout.extend(non_lexical_rules.iter().map(|(k, v)| (k.clone(), *v)));
        combined_rules_for_stdout.extend(lexical_rules.iter().map(|(k, v)| (k.clone(), *v)));
        combined_rules_for_stdout.sort_by_key(|(rule_key, _)| rule_key.clone());
    }


    if let Some(prefix) = output_prefix {
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

        // non-lexical rules "LHS -> RHS PROB" format
        let mut sorted_non_lexical: Vec<_> = non_lexical_rules.iter().collect();
        sorted_non_lexical.sort_by_key(|(rule_key, _)| *rule_key);
        for (rule, count) in sorted_non_lexical {
             write_rule_line_arrow_format(&mut rules_writer, rule, *count, lhs_totals)?;
        }

        // lexical rules "LHS RHS PROB" format
        let mut sorted_lexical: Vec<_> = lexical_rules.iter().collect();
        sorted_lexical.sort_by_key(|(rule_key, _)| *rule_key);
        for (rule, count) in sorted_lexical {
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
                     let output_line = format!("{} {} {}", lhs_trimmed, rhs_trimmed, relative_frequency);
                     writeln!(lexicon_writer, "{}", output_line)?;

                     if unique_words_for_output.insert(rhs_trimmed.to_string()) {
                        writeln!(words_writer, "{}", rhs_trimmed)?;
                     }

                 } else {
                     eprintln!(
                         "Internal error: Could not find total count for LHS '{}' from lexical rule '{}'. Skipping lexicon output.",
                         lhs_trimmed, rule
                     );
                 }

             } else {
                 eprintln!(
                     "Warning: Lexical rule format incorrect, skipping lexicon output: {}",
                     rule
                 );
             }
        }

        rules_writer.flush()?;
        lexicon_writer.flush()?;
        words_writer.flush()?;

        eprintln!(
            "Successfully wrote: {}, {}, {}",
            rules_output_filename, lexicon_output_filename, words_output_filename
        );

    } else {
        eprintln!("Writing combined PCFG rules to standard output...");
        let stdout = io::stdout();
        let mut writer = BufWriter::new(stdout.lock());

        for (rule, count) in combined_rules_for_stdout {
             write_rule_line_arrow_format(&mut writer, &rule, count, lhs_totals)?;
        }

        writer.flush()?;
        eprintln!("Finished writing to standard output.");
    }

    Ok(())
}

// LHS -> RHS PROB
fn write_rule_line_arrow_format<W: Write>(
    writer: &mut BufWriter<W>,
    rule: &str,
    count: u64,
    lhs_totals: &HashMap<String, u64>,
) -> io::Result<()> {
    if let Some((lhs, _)) = rule.split_once(" -> ") {
        let lhs_trimmed = lhs.trim();
        if let Some(total_count) = lhs_totals.get(lhs_trimmed) {
            let relative_frequency = if *total_count > 0 {
                count as f64 / *total_count as f64
            } else {
                0.0
            };
            let output_line = format!("{} {}", rule, relative_frequency);
            writeln!(writer, "{}", output_line)?;
        } else {
             eprintln!(
                 "Internal error: LHS '{}' not found in totals for rule '{}'. Skipping output.",
                 lhs_trimmed, rule
             );
        }
    } else {
         eprintln!(
             "Warning: Rule format incorrect, skipping output: {}",
             rule
         );
    }
    Ok(())
}