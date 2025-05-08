use crate::structs::Node; 
use crate::parser::parse_tree;
use crate::rules::extract_rules;
use crate::output::write_pcfg_output;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Write}; 
use tempfile::tempdir;
use crate::grammar::{load_grammar, Grammar, LexicalRule, BinaryRule, UnaryRule};
use crate::cyk::parse_sentence; 
use std::path::PathBuf;

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

// --- Tests for grammar loading ---

fn create_test_grammar_files(dir: &tempfile::TempDir, rules_content: &str, lexicon_content: &str) -> io::Result<(PathBuf, PathBuf)> {
    let rules_path = dir.path().join("test.rules");
    let lexicon_path = dir.path().join("test.lexicon");
    fs::write(&rules_path, rules_content)?;
    fs::write(&lexicon_path, lexicon_content)?;
    Ok((rules_path, lexicon_path))
}

#[test]
fn load_grammar_simple_valid() -> io::Result<()> {
    let dir = tempdir()?;
    let rules_content = "ROOT -> S 1.0\nS -> NP VP 0.9\nNP -> DT NN 0.7\nVP -> V NP 0.8\nVP -> V 0.1\nNN -> NNP 0.1";
    let lexicon_content = "DT the 1.0\nNN dog 0.5\nNN cat 0.3\nNNP Max 1.0\nV chased 0.9\nV ran 0.1";
    let (rules_path, lexicon_path) = create_test_grammar_files(&dir, rules_content, lexicon_content)?;

    let grammar = load_grammar(&rules_path, &lexicon_path)?;

    assert!(grammar.non_terminals.contains("ROOT"));
    assert!(grammar.non_terminals.contains("S"));
    assert!(grammar.non_terminals.contains("NP"));
    assert!(grammar.non_terminals.contains("VP"));
    assert!(grammar.non_terminals.contains("DT"));
    assert!(grammar.non_terminals.contains("NN"));
    assert!(grammar.non_terminals.contains("NNP"));
    assert!(grammar.non_terminals.contains("V"));
    assert_eq!(grammar.non_terminals.len(), 8);

    assert!(grammar.terminals.contains("the"));
    assert!(grammar.terminals.contains("dog"));
    assert!(grammar.terminals.contains("cat"));
    assert!(grammar.terminals.contains("Max"));
    assert!(grammar.terminals.contains("chased"));
    assert!(grammar.terminals.contains("ran"));
    assert_eq!(grammar.terminals.len(), 6);

    assert_eq!(grammar.start_symbol, "ROOT");

    let dt_rules = grammar.lexical_rules_by_rhs.get("the").unwrap();
    assert_eq!(dt_rules.len(), 1);
    assert_eq!(dt_rules[0].lhs, "DT");

    let s_rules = grammar.binary_rules_by_children.get(&("NP".to_string(), "VP".to_string())).unwrap();
    assert_eq!(s_rules.len(), 1);
    assert_eq!(s_rules[0].lhs, "S");
    assert_eq!(s_rules[0].probability, 0.9);

    let unary_nn_rules = grammar.unary_rules_by_rhs.get("NNP").unwrap();
    assert_eq!(unary_nn_rules.len(), 1);
    assert_eq!(unary_nn_rules[0].lhs, "NN");
    assert_eq!(unary_nn_rules[0].probability, 0.1);

    Ok(())
}

#[test]
fn load_grammar_malformed_prob() -> io::Result<()> {
    let dir = tempdir()?;
    let rules_content = "S -> NP VP 1.0";
    let lexicon_content = "DT the not_a_number";
    let (rules_path, lexicon_path) = create_test_grammar_files(&dir, rules_content, lexicon_content)?;

    let result = load_grammar(&rules_path, &lexicon_path);
    assert!(result.is_err());
    Ok(())
}

#[test]
fn load_grammar_malformed_rule_format() -> io::Result<()> {
    let dir = tempdir()?;
    let rules_content = "S NP VP 1.0\nROOT -> S 0.8\nS -> X Y 0.2";
    let lexicon_content = "DT the 1.0\nX x_term 1.0\nY y_term 1.0";
    let (rules_path, lexicon_path) = create_test_grammar_files(&dir, rules_content, lexicon_content)?;

    let grammar = load_grammar(&rules_path, &lexicon_path)?;

    assert_eq!(grammar.binary_rules_by_children.values().flatten().count(), 1, "Only S -> X Y should be a valid binary rule");
    assert!(grammar.binary_rules_by_children.contains_key(&("X".to_string(), "Y".to_string())));

    assert_eq!(grammar.unary_rules_by_lhs.values().flatten().count(), 1, "Only ROOT -> S should be a valid unary rule");
    assert!(grammar.unary_rules_by_lhs.contains_key("ROOT"));


    assert!(!grammar.lexical_rules_by_rhs.is_empty(), "Lexicon should be loaded");
    assert!(grammar.lexical_rules_by_rhs.contains_key("the"));
    assert!(grammar.lexical_rules_by_rhs.contains_key("x_term"));
    assert!(grammar.lexical_rules_by_rhs.contains_key("y_term"));

    assert!(grammar.non_terminals.contains("ROOT"));
    assert!(grammar.non_terminals.contains("S"));
    assert!(grammar.non_terminals.contains("X"));
    assert!(grammar.non_terminals.contains("Y"));
    assert!(grammar.non_terminals.contains("DT"));
    assert!(!grammar.non_terminals.contains("NP"), "'NP' should not be added because the rule is invalid");
    assert!(!grammar.non_terminals.contains("VP"), "'VP' should not be added because the rule is invalid");


    assert_eq!(grammar.start_symbol, "ROOT", "Start symbol should be 'ROOT' from the valid rule");
    Ok(())
}

// --- Tests for CYK parsing ---

fn create_test_grammar() -> Grammar {
     let mut grammar = Grammar {
        non_terminals: HashSet::new(),
        terminals: HashSet::new(),
        start_symbol: "S".to_string(),
        lexical_rules_by_rhs: HashMap::new(),
        unary_rules_by_rhs: HashMap::new(),
        binary_rules_by_children: HashMap::new(),
        unary_rules_by_lhs: HashMap::new(),
     };

     for nt in ["S", "NP", "VP", "PP", "DT", "NN", "V", "P"].iter() {
        grammar.non_terminals.insert(nt.to_string());
     }
      for t in ["the", "a", "man", "dog", "telescope", "saw", "with", "ran"].iter() {
        grammar.terminals.insert(t.to_string());
     }

     let rules = vec![
         LexicalRule { lhs: "DT".to_string(), rhs: "the".to_string(), probability: 1.0 },
         LexicalRule { lhs: "DT".to_string(), rhs: "a".to_string(), probability: 1.0 },
         LexicalRule { lhs: "NN".to_string(), rhs: "man".to_string(), probability: 1.0 },
         LexicalRule { lhs: "NN".to_string(), rhs: "dog".to_string(), probability: 1.0 },
         LexicalRule { lhs: "NN".to_string(), rhs: "telescope".to_string(), probability: 1.0 },
         LexicalRule { lhs: "V".to_string(), rhs: "saw".to_string(), probability: 1.0 },
         LexicalRule { lhs: "V".to_string(), rhs: "ran".to_string(), probability: 1.0 },
         LexicalRule { lhs: "P".to_string(), rhs: "with".to_string(), probability: 1.0 },
     ];
     for rule in rules {
         grammar.lexical_rules_by_rhs.entry(rule.rhs.clone()).or_default().push(rule);
     }

     let bin_rules = vec![
         BinaryRule { lhs: "S".to_string(), rhs1: "NP".to_string(), rhs2: "VP".to_string(), probability: 1.0 },
         BinaryRule { lhs: "NP".to_string(), rhs1: "DT".to_string(), rhs2: "NN".to_string(), probability: 1.0 },
         BinaryRule { lhs: "VP".to_string(), rhs1: "V".to_string(), rhs2: "NP".to_string(), probability: 0.7 },
         BinaryRule { lhs: "VP".to_string(), rhs1: "VP".to_string(), rhs2: "PP".to_string(), probability: 0.5 },
         BinaryRule { lhs: "NP".to_string(), rhs1: "NP".to_string(), rhs2: "PP".to_string(), probability: 0.2 },
         BinaryRule { lhs: "PP".to_string(), rhs1: "P".to_string(), rhs2: "NP".to_string(), probability: 1.0 },
     ];
     for rule in bin_rules {
          grammar.binary_rules_by_children.entry((rule.rhs1.clone(), rule.rhs2.clone())).or_default().push(rule);
     }

     let unary_rules = vec![
         UnaryRule { lhs: "VP".to_string(), rhs: "V".to_string(), probability: 0.1 }
     ];
      for rule in unary_rules {
          grammar.unary_rules_by_rhs.entry(rule.rhs.clone()).or_default().push(rule.clone());
          grammar.unary_rules_by_lhs.entry(rule.lhs.clone()).or_default().push(rule);
      }
     grammar
}

#[test]
fn cyk_parse_simple_sentence() {
    let mut simple_grammar = create_test_grammar();
    simple_grammar.binary_rules_by_children.retain(|_, rules| {
        rules.retain(|r| r.lhs != "VP" || r.rhs2 != "PP");
        rules.retain(|r| r.lhs != "NP" || r.rhs2 != "PP");
        !rules.is_empty()
    });
     simple_grammar.unary_rules_by_rhs.clear();
     simple_grammar.unary_rules_by_lhs.clear();
      let vp_v_rule = UnaryRule { lhs: "VP".to_string(), rhs: "V".to_string(), probability: 1.0 };
      simple_grammar.unary_rules_by_rhs.entry("V".to_string()).or_default().push(vp_v_rule.clone());
      simple_grammar.unary_rules_by_lhs.entry("VP".to_string()).or_default().push(vp_v_rule);

    let sentence = vec!["the".to_string(), "dog".to_string(), "ran".to_string()];
    let expected_tree = "(S (NP (DT the) (NN dog)) (VP (V ran)))";
    let result_simple = parse_sentence(&simple_grammar, &sentence, "S");
    assert_eq!(result_simple, expected_tree);
}

#[test]
fn cyk_parse_longer_sentence_ambiguous() {
     let grammar = create_test_grammar();
     let sentence = vec!["the".to_string(), "man".to_string(), "saw".to_string(), "a".to_string(), "dog".to_string(), "with".to_string(), "a".to_string(), "telescope".to_string()];
     let result = parse_sentence(&grammar, &sentence, "S");
      let expected_tree_vp_attach = "(S (NP (DT the) (NN man)) (VP (VP (V saw) (NP (DT a) (NN dog))) (PP (P with) (NP (DT a) (NN telescope)))))";
     assert_eq!(result, expected_tree_vp_attach);
}


#[test]
fn cyk_parse_no_parse() {
    let grammar = create_test_grammar();
    let sentence = vec!["the".to_string(), "cat".to_string(), "barked".to_string()];
    let expected_output = "(NOPARSE the cat barked)";
    let result = parse_sentence(&grammar, &sentence, "S");
    assert_eq!(result, expected_output);
}

#[test]
fn cyk_parse_no_parse_valid_words_wrong_structure() {
    let mut grammar = create_test_grammar();
    grammar.binary_rules_by_children.retain(|key, _rules| {
        key != &("DT".to_string(), "NN".to_string())
    });

    let sentence = vec!["the".to_string(), "dog".to_string(), "ran".to_string()];
    let expected_output = "(NOPARSE the dog ran)";

    let result = parse_sentence(&grammar, &sentence, "S");
    assert_eq!(result, expected_output);
}


#[test]
fn cyk_parse_empty_sentence() {
    let grammar = create_test_grammar();
    let sentence: Vec<String> = vec![];
    let expected_output = "(NOPARSE)";
    let result = parse_sentence(&grammar, &sentence, "S");
    assert_eq!(result, expected_output);
}