use clap::Parser;
use std::fs::{self, File};
use std::io::{self, BufRead, BufWriter, Write};
use std::collections::{HashMap, HashSet};
use std::iter::Peekable;
use std::str::Chars;

// --- Data Structures ---

#[derive(Debug, Clone, PartialEq)]
struct Node {
    label: String,
    children: Vec<Node>,
}

impl Node {
    fn is_terminal(&self) -> bool {
        self.children.is_empty()
    }
}

#[derive(Debug)]
struct ParseError(String);

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


// --- Main Logic ---
fn main() -> io::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Induce(args) => {
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

            write_pcfg_output(&non_lexical_rules, &lexical_rules, &lhs_totals, args.grammar_output_prefix,)?;

            eprintln!("PCFG induction complete.");
        }
    }

    Ok(())
}


// --- Tree Parsing  ---

fn parse_tree(input: &str) -> Result<Node, ParseError> {
    let mut chars = input.trim().chars().peekable();
    parse_node(&mut chars)
}

fn parse_node(chars: &mut Peekable<Chars>) -> Result<Node, ParseError> {
    match chars.next() {
        Some('(') => (),
        _ => return Err(ParseError("Expected '(' at start of node".to_string())),
    }
    consume_whitespace(chars);
    let label = parse_label(chars)?;
    consume_whitespace(chars);
    let mut children = Vec::new();
    while let Some(&c) = chars.peek() {
        if c == ')' {
            break;
        } else if c == '(' {
            children.push(parse_node(chars)?);
        } else {
             children.push(parse_terminal_leaf(chars)?);
        }
        consume_whitespace(chars);
    }
    match chars.next() {
        Some(')') => (),
        _ => return Err(ParseError(format!("Expected ')' to close node labeled '{}'", label))),
    }
    Ok(Node { label, children })
}


fn parse_label(chars: &mut Peekable<Chars>) -> Result<String, ParseError> {
    let mut label = String::new();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() || c == '(' || c == ')' {
            break;
        }
        label.push(chars.next().unwrap());
    }
    if label.is_empty() {
        Err(ParseError("Node label cannot be empty".to_string()))
    } else {
        Ok(label)
    }
}

fn parse_terminal_leaf(chars: &mut Peekable<Chars>) -> Result<Node, ParseError> {
     let label = parse_label(chars)?;
     Ok(Node { label, children: vec![] })
}


fn consume_whitespace(chars: &mut Peekable<Chars>) {
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
}


// --- Rule Extraction---

fn extract_rules(
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


// --- Output Writing---

fn write_pcfg_output(
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
            let output_line = format!("{} {:.6}", rule, relative_frequency);
            writeln!(writer, "{}", output_line)?;
        } 
    } 
    Ok(())
}


// --- Test Module ---
#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    // --- Tests for parse_tree---

    #[test]
    fn parse_simple_terminal() {
        assert!(parse_tree("word").is_err());
        assert!(parse_tree("(word)").is_ok());
        assert_eq!(parse_tree("(word)").unwrap(), Node {label: "word".to_string(), children: vec![]});
    }

     #[test]
    fn parse_simple_pre_terminal() {
        let expected = Node {
            label: "NN".to_string(),
            children: vec![Node { label: "dog".to_string(), children: vec![] }],
        };
        assert_eq!(parse_tree("(NN dog)").unwrap(), expected);
    }

    #[test]
    fn parse_simple_non_terminal() {
        let expected = Node {
            label: "NP".to_string(),
            children: vec![
                Node {
                    label: "DT".to_string(),
                    children: vec![Node { label: "the".to_string(), children: vec![] }],
                },
                Node {
                    label: "NN".to_string(),
                    children: vec![Node { label: "dog".to_string(), children: vec![] }],
                },
            ],
        };
        assert_eq!(parse_tree("(NP (DT the) (NN dog))").unwrap(), expected);
    }

    #[test]
    fn parse_nested() {
         let input = "(S (NP (DT The) (NN dog)) (VP (VBD chased) (NP (DT a) (NN cat))))";
         let expected = Node {
             label: "S".to_string(),
             children: vec![
                 Node { 
                     label: "NP".to_string(),
                     children: vec![
                         Node { label: "DT".to_string(), children: vec![Node{label:"The".to_string(), children:vec![]}] },
                         Node { label: "NN".to_string(), children: vec![Node{label:"dog".to_string(), children:vec![]}] }
                     ]
                 },
                 Node {
                     label: "VP".to_string(),
                     children: vec![
                         Node { label: "VBD".to_string(), children: vec![Node{label:"chased".to_string(), children:vec![]}] },
                         Node { 
                             label: "NP".to_string(),
                             children: vec![
                                 Node { label: "DT".to_string(), children: vec![Node{label:"a".to_string(), children:vec![]}] },
                                 Node { label: "NN".to_string(), children: vec![Node{label:"cat".to_string(), children:vec![]}] }
                             ]
                         }
                     ]
                 }
             ]
         };
         assert_eq!(parse_tree(input).unwrap(), expected);
    }

     #[test]
    fn parse_with_extra_whitespace() {
        let expected = Node {
            label: "NP".to_string(),
            children: vec![
                Node {
                    label: "DT".to_string(),
                    children: vec![Node { label: "the".to_string(), children: vec![] }],
                },
                Node {
                    label: "NN".to_string(),
                    children: vec![Node { label: "dog".to_string(), children: vec![] }],
                },
            ],
        };
        assert_eq!(parse_tree(" ( NP ( DT the ) ( NN dog ) ) ").unwrap(), expected);
         assert_eq!(parse_tree("(NP(DT the)(NN dog))").unwrap(), expected);
    }


    #[test]
    fn parse_ptb_example() {
         let input = "(ROOT (S (`` ``) (NP-SBJ (DT Any) (NN fool)) (VP (MD can) (VP (VB publish) (NP (DT a) (JJ money-losing) (NN magazine)))) (. .)))";
         assert!(parse_tree(input).is_ok());
    }

    #[test]
    fn parse_error_unbalanced() {
        assert!(parse_tree("(NP (DT the)").is_err());
        assert!(parse_tree("NP (DT the))").is_err());
         assert!(parse_tree("(NP (DT the").is_err());
         assert!(parse_tree("())").is_err());
         assert!(parse_tree("(()())").is_err());
    }

     #[test]
    fn parse_error_missing_label() {
        assert!(parse_tree("()").is_err());
         assert!(parse_tree("(())").is_err());
         assert!(parse_tree("(A ())").is_err());
    }


    // --- Tests for extract_rules ---

    #[test]
    fn extract_rules_simple() {
        let tree = parse_tree("(NP (DT the) (NN dog))").unwrap();
        let mut non_lex: HashMap<String, u64> = HashMap::new();
        let mut lex: HashMap<String, u64> = HashMap::new();
        extract_rules(&tree, &mut non_lex, &mut lex);

        let mut expected_non_lex: HashMap<String, u64> = HashMap::new();
        expected_non_lex.insert("NP -> DT NN".to_string(), 1);

        let mut expected_lex: HashMap<String, u64> = HashMap::new();
        expected_lex.insert("DT -> the".to_string(), 1);
        expected_lex.insert("NN -> dog".to_string(), 1);

        assert_eq!(non_lex, expected_non_lex);
        assert_eq!(lex, expected_lex);
    }

    #[test]
    fn extract_rules_nested() {
         let tree = parse_tree("(S (NP (DT the) (NN dog)) (VP (V runs)))").unwrap();
         let mut non_lex: HashMap<String, u64> = HashMap::new();
         let mut lex: HashMap<String, u64> = HashMap::new();
         extract_rules(&tree, &mut non_lex, &mut lex);

        let mut expected_non_lex_corrected: HashMap<String, u64> = HashMap::new();
        expected_non_lex_corrected.insert("S -> NP VP".to_string(), 1);
        expected_non_lex_corrected.insert("NP -> DT NN".to_string(), 1);
        expected_non_lex_corrected.insert("VP -> V".to_string(), 1);


        let mut expected_lex_corrected: HashMap<String, u64> = HashMap::new();
        expected_lex_corrected.insert("DT -> the".to_string(), 1);
        expected_lex_corrected.insert("NN -> dog".to_string(), 1);
        expected_lex_corrected.insert("V -> runs".to_string(), 1);

        assert_eq!(non_lex, expected_non_lex_corrected);
        assert_eq!(lex, expected_lex_corrected);
    }

    #[test]
    fn extract_rules_ptb_example() {
        let tree = parse_tree("(ROOT (S (`` ``) (NP-SBJ (DT Any) (NN fool)) (VP (MD can) (VP (VB publish) (NP (DT a) (JJ money-losing) (NN magazine)))) (. .)))").unwrap();
        let mut non_lex: HashMap<String, u64> = HashMap::new();
        let mut lex: HashMap<String, u64> = HashMap::new();
        extract_rules(&tree, &mut non_lex, &mut lex);

        assert_eq!(*non_lex.get("ROOT -> S").unwrap(), 1);
        assert_eq!(*non_lex.get("S -> `` NP-SBJ VP .").unwrap(), 1);
        assert_eq!(*non_lex.get("NP-SBJ -> DT NN").unwrap(), 1);
        assert_eq!(*non_lex.get("VP -> MD VP").unwrap(), 1);
         assert_eq!(*non_lex.get("VP -> VB NP").unwrap(), 1);
        assert_eq!(*non_lex.get("NP -> DT JJ NN").unwrap(), 1);

        assert_eq!(*lex.get("`` -> ``").unwrap(), 1);
        assert_eq!(*lex.get("DT -> Any").unwrap(), 1);
        assert_eq!(*lex.get("NN -> fool").unwrap(), 1);
        assert_eq!(*lex.get("MD -> can").unwrap(), 1);
        assert_eq!(*lex.get("VB -> publish").unwrap(), 1);
        assert_eq!(*lex.get("DT -> a").unwrap(), 1);
        assert_eq!(*lex.get("JJ -> money-losing").unwrap(), 1);
        assert_eq!(*lex.get("NN -> magazine").unwrap(), 1);
         assert_eq!(*lex.get(". -> .").unwrap(), 1);

        assert_eq!(lex.len(), 9);
        assert_eq!(non_lex.len(), 6);
    }


    // --- Tests for write_pcfg_output ---

    #[test]
    fn write_output_to_files_tree_based() -> io::Result<()> {
        let dir = tempdir()?;
        let current_dir = std::env::current_dir()?;
        std::env::set_current_dir(dir.path())?;

        let mut non_lexical_rules: HashMap<String, u64> = HashMap::new();
        non_lexical_rules.insert("S -> NP VP".to_string(), 10);
        non_lexical_rules.insert("NP -> DT NN".to_string(), 8);
        non_lexical_rules.insert("VP -> V NP".to_string(), 9);
         non_lexical_rules.insert("NP -> NNP".to_string(), 2);


        let mut lexical_rules: HashMap<String, u64> = HashMap::new();
        lexical_rules.insert("DT -> the".to_string(), 5);
        lexical_rules.insert("NN -> dog".to_string(), 3);
        lexical_rules.insert("NN -> cat".to_string(), 3);
        lexical_rules.insert("V -> chased".to_string(), 9);
        lexical_rules.insert("NNP -> Peter".to_string(), 2);


        let mut lhs_totals: HashMap<String, u64> = HashMap::new();
        for (rule, count) in non_lexical_rules.iter().chain(lexical_rules.iter()) {
             if let Some((lhs, _)) = rule.split_once(" -> ") {
                 *lhs_totals.entry(lhs.trim().to_string()).or_insert(0) += count;
             }
        }

        let output_prefix = "test_grammar_tree".to_string();

        write_pcfg_output(
            &non_lexical_rules,
            &lexical_rules,
            &lhs_totals,
            Some(output_prefix.clone()),
        )?;

        let rules_content = fs::read_to_string(format!("{}.rules", output_prefix))?;
        let lexicon_content = fs::read_to_string(format!("{}.lexicon", output_prefix))?;
        let words_content = fs::read_to_string(format!("{}.words", output_prefix))?;

        let expected_rules = [
            "NP -> DT NN 0.800000",
            "NP -> NNP 0.200000",
            "S -> NP VP 1.000000",
            "VP -> V NP 1.000000",
        ]
        .join("\n") + "\n";

        let expected_lexicon = [
            "DT the 1.000000",    // 5 / 5
            "NN cat 0.500000",    // 3 / 6
            "NN dog 0.500000",    // 3 / 6
            "NNP Peter 1.000000", // 2 / 2
            "V chased 1.000000",  // 9 / 9
        ]
        .join("\n") + "\n";

         let expected_words_vec = vec!["Peter", "cat", "chased", "dog", "the"];
         let mut sorted_expected_words = expected_words_vec.clone();
         sorted_expected_words.sort();
         let expected_words_string = sorted_expected_words.join("\n") + "\n";

         let mut actual_words: Vec<String> = words_content.lines().map(String::from).collect();
         actual_words.sort();
         let actual_words_string = actual_words.join("\n") + "\n";


         let mut actual_rules_lines: Vec<&str> = rules_content.lines().collect();
         actual_rules_lines.sort();
         let mut expected_rules_lines: Vec<&str> = expected_rules.lines().collect();
         expected_rules_lines.sort();

         let mut actual_lexicon_lines: Vec<&str> = lexicon_content.lines().collect();
         actual_lexicon_lines.sort();
         let mut expected_lexicon_lines: Vec<&str> = expected_lexicon.lines().collect();
         expected_lexicon_lines.sort();


        assert_eq!(actual_rules_lines, expected_rules_lines, "Mismatch in .rules content");
        assert_eq!(actual_lexicon_lines, expected_lexicon_lines, "Mismatch in .lexicon content");
        assert_eq!(actual_words_string, expected_words_string, "Mismatch in .words content");


        std::env::set_current_dir(current_dir)?;
        dir.close()?;
        Ok(())
    }

    #[test]
    fn write_output_zero_total_count_tree() -> io::Result<()> {
        let dir = tempdir()?;
        let current_dir = std::env::current_dir()?;
        std::env::set_current_dir(dir.path())?;

        let mut non_lex_zero = HashMap::new();
        non_lex_zero.insert("S -> NP VP".to_string(), 0); 

        let mut lex_zero = HashMap::new();
        lex_zero.insert("NN -> word".to_string(), 0); 

        let mut lhs_totals: HashMap<String, u64> = HashMap::new();
         lhs_totals.insert("S".to_string(), 0); 
         lhs_totals.insert("NN".to_string(), 0); 


        let output_prefix = "zero_test_tree".to_string();
        write_pcfg_output(&non_lex_zero, &lex_zero, &lhs_totals, Some(output_prefix.clone()))?;

        let rules_content = fs::read_to_string(format!("{}.rules", output_prefix))?;
        let expected_rules = "S -> NP VP 0.000000\n";
        assert_eq!(rules_content, expected_rules);

        let lexicon_content = fs::read_to_string(format!("{}.lexicon", output_prefix))?;
        let expected_lexicon = "NN word 0.000000\n";
        assert_eq!(lexicon_content, expected_lexicon);

        let words_content = fs::read_to_string(format!("{}.words", output_prefix))?;
        assert_eq!(words_content, "word\n");


        std::env::set_current_dir(current_dir)?;
        dir.close()?;
        Ok(())
    }

} // End of the test module