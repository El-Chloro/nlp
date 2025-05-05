use crate::structs::{Node, ParseError}; 
use crate::parser::parse_tree;
use crate::rules::extract_rules;
use crate::output::write_pcfg_output;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Write}; 
use tempfile::tempdir;

// --- Tests for parse_tree---

#[test]
fn parse_simple_terminal() {
    assert!(parse_tree("word").is_err());
    let parsed_node = parse_tree("(word)");
    assert!(parsed_node.is_ok());
    assert_eq!(parsed_node.unwrap(), Node {label: "word".to_string(), children: vec![]});
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

fn normalize_floats(s: &str) -> String {
    s.lines()
        .map(|line| {
            if let Some((before, after)) = line.rsplit_once(' ') {
                if let Ok(num) = after.parse::<f64>() {
                    format!("{} {:.6}", before, num)
                } else {
                    line.to_string()
                }
            } else {
                line.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}


#[test]
fn write_output_to_files_tree_based() -> io::Result<()> {
    let dir = tempdir()?;

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
    lhs_totals.insert("S".to_string(), 10);
    lhs_totals.insert("NP".to_string(), 10);
    lhs_totals.insert("VP".to_string(), 9);
    lhs_totals.insert("DT".to_string(), 5);
    lhs_totals.insert("NN".to_string(), 6); 
    lhs_totals.insert("V".to_string(), 9);
    lhs_totals.insert("NNP".to_string(), 2);


    let output_prefix = dir.path().join("test_grammar_tree").to_str().unwrap().to_string();

    write_pcfg_output(
        &non_lexical_rules,
        &lexical_rules,
        &lhs_totals,
        Some(output_prefix.clone()),
    )?;

    let rules_content = fs::read_to_string(format!("{}.rules", output_prefix))?;
    let lexicon_content = fs::read_to_string(format!("{}.lexicon", output_prefix))?;
    let words_content = fs::read_to_string(format!("{}.words", output_prefix))?;

    let expected_rules_vec = vec![
        "NP -> DT NN 0.800000",
        "NP -> NNP 0.200000",
        "S -> NP VP 1.000000", 
        "VP -> V NP 1.000000", 
    ];
    let mut sorted_expected_rules = expected_rules_vec.clone();
    sorted_expected_rules.sort();
    let expected_rules_string = sorted_expected_rules.join("\n") + "\n";


    let expected_lexicon_vec = vec![
        "DT the 1.000000",    // 5 / 5
        "NN cat 0.500000",    // 3 / 6
        "NN dog 0.500000",    // 3 / 6
        "NNP Peter 1.000000", // 2 / 2
        "V chased 1.000000",  // 9 / 9
    ];
    let mut sorted_expected_lexicon = expected_lexicon_vec.clone();
    sorted_expected_lexicon.sort();
    let expected_lexicon_string = sorted_expected_lexicon.join("\n") + "\n";


     let expected_words_vec = vec!["Peter", "cat", "chased", "dog", "the"];
     let mut sorted_expected_words = expected_words_vec.clone();
     sorted_expected_words.sort();
     let expected_words_string = sorted_expected_words.join("\n") + "\n";

     let mut actual_words: Vec<String> = words_content.lines().map(String::from).collect();
     actual_words.sort();
     let actual_words_string = actual_words.join("\n") + "\n";


     let mut actual_rules_lines: Vec<String> = rules_content.lines().map(normalize_floats).collect();
     actual_rules_lines.sort();
     let actual_rules_string = actual_rules_lines.join("\n") + "\n";


     let mut actual_lexicon_lines: Vec<String> = lexicon_content.lines().map(normalize_floats).collect();
     actual_lexicon_lines.sort();
     let actual_lexicon_string = actual_lexicon_lines.join("\n") + "\n";


    assert_eq!(actual_rules_string, expected_rules_string, "Mismatch in .rules content");
    assert_eq!(actual_lexicon_string, expected_lexicon_string, "Mismatch in .lexicon content");
    assert_eq!(actual_words_string, expected_words_string, "Mismatch in .words content");

    dir.close()?;
    Ok(())
}


#[test]
fn write_output_zero_total_count_tree() -> io::Result<()> {
    let dir = tempdir()?;

    let mut non_lex_zero = HashMap::new();
    non_lex_zero.insert("S -> NP VP".to_string(), 0); 

    let mut lex_zero = HashMap::new();
    lex_zero.insert("NN -> word".to_string(), 0); 

    let mut lhs_totals: HashMap<String, u64> = HashMap::new();
     lhs_totals.insert("S".to_string(), 0); 
     lhs_totals.insert("NN".to_string(), 0); 


    let output_prefix = dir.path().join("zero_test_tree").to_str().unwrap().to_string();

    write_pcfg_output(&non_lex_zero, &lex_zero, &lhs_totals, Some(output_prefix.clone()))?;

    let rules_content = fs::read_to_string(format!("{}.rules", output_prefix))?;
    let expected_rules = normalize_floats("S -> NP VP 0.000000\n");
    assert_eq!(normalize_floats(&rules_content), expected_rules);

    let lexicon_content = fs::read_to_string(format!("{}.lexicon", output_prefix))?;
    let expected_lexicon = normalize_floats("NN word 0.000000\n");
    assert_eq!(normalize_floats(&lexicon_content), expected_lexicon);

    let words_content = fs::read_to_string(format!("{}.words", output_prefix))?;
    assert_eq!(words_content.trim(), "word"); 

    dir.close()?;
    Ok(())
}