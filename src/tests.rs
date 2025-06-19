use crate::structs::Node;
use crate::parser::parse_tree;
use crate::rules::extract_rules;
use crate::output::{write_pcfg_output, tree_to_string};
use crate::transformations::{debinarise_node, collect_leaves, replace_rare_words, restore_words};
use std::collections::HashMap;
use std::fs;
use std::io;
use tempfile::tempdir;
use crate::grammar::{load_grammar, Grammar, LexicalRule, UnaryRule, BinaryRule};
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
    assert_eq!(grammar.start_symbol, "ROOT");

    let dt_id = grammar.non_terminal_to_id["DT"];
    let the_rules = grammar.lexical_rules_by_rhs.get("the").unwrap();
    assert_eq!(the_rules.len(), 1);
    assert_eq!(the_rules[0].lhs_id, dt_id);

    let s_id = grammar.non_terminal_to_id["S"];
    let np_id = grammar.non_terminal_to_id["NP"];
    let vp_id = grammar.non_terminal_to_id["VP"];
    let s_rules = grammar.binary_rules_by_children.get(&(np_id, vp_id)).unwrap();
    assert_eq!(s_rules.len(), 1);
    assert_eq!(s_rules[0].lhs_id, s_id);
    assert!((s_rules[0].cost - (-(0.9_f64.ln()))).abs() < 1e-9);

    let nn_id = grammar.non_terminal_to_id["NN"];
    let nnp_id = grammar.non_terminal_to_id["NNP"];
    let unary_nn_rules = grammar.unary_rules_by_rhs.get(&nnp_id).unwrap();
    assert_eq!(unary_nn_rules.len(), 1);
    assert_eq!(unary_nn_rules[0].lhs_id, nn_id);
    assert!((unary_nn_rules[0].cost - (-(0.1_f64.ln()))).abs() < 1e-9);


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

    let x_id = grammar.non_terminal_to_id["X"];
    let y_id = grammar.non_terminal_to_id["Y"];
    let root_id = grammar.non_terminal_to_id["ROOT"];


    assert_eq!(grammar.binary_rules_by_children.values().flatten().count(), 1, "Only S -> X Y should be a valid binary rule");
    assert!(grammar.binary_rules_by_children.contains_key(&(x_id, y_id)));

    assert_eq!(grammar.unary_rules_by_lhs.values().flatten().count(), 1, "Only ROOT -> S should be a valid unary rule");
    assert!(grammar.unary_rules_by_lhs.contains_key(&root_id));


    assert!(!grammar.lexical_rules_by_rhs.is_empty(), "Lexicon should be loaded");
    assert!(grammar.lexical_rules_by_rhs.contains_key("the"));
    assert!(grammar.lexical_rules_by_rhs.contains_key("x_term"));
    assert!(grammar.lexical_rules_by_rhs.contains_key("y_term"));

    assert!(!grammar.non_terminals.contains("NP"), "'NP' should not be added because the rule is invalid");
    assert!(!grammar.non_terminals.contains("VP"), "'VP' should not be added because the rule is invalid");


    assert_eq!(grammar.start_symbol, "ROOT", "Start symbol should be 'ROOT' from the valid rule");
    Ok(())
}


// --- Test setup for CYK and Transformations ---
fn setup_test_grammar() -> Grammar {
    let mut grammar = Grammar::new();
    let s = grammar.get_or_intern_non_terminal("S");
    let np = grammar.get_or_intern_non_terminal("NP");
    let vp = grammar.get_or_intern_non_terminal("VP");
    let pp = grammar.get_or_intern_non_terminal("PP");
    let dt = grammar.get_or_intern_non_terminal("DT");
    let nn = grammar.get_or_intern_non_terminal("NN");
    let v = grammar.get_or_intern_non_terminal("V");
    let p = grammar.get_or_intern_non_terminal("P");

    grammar.start_symbol = "S".to_string();
    grammar.terminals.extend(["the", "a", "man", "dog", "telescope", "saw", "with", "ran"].iter().map(|s| s.to_string()));

    // Lexical Rules
    grammar.add_lexical_rule(LexicalRule { lhs_id: dt, rhs: "the".to_string(), cost: 0.0 });
    grammar.add_lexical_rule(LexicalRule { lhs_id: dt, rhs: "a".to_string(), cost: 0.0 });
    grammar.add_lexical_rule(LexicalRule { lhs_id: nn, rhs: "man".to_string(), cost: 0.0 });
    grammar.add_lexical_rule(LexicalRule { lhs_id: nn, rhs: "dog".to_string(), cost: 0.0 });
    grammar.add_lexical_rule(LexicalRule { lhs_id: nn, rhs: "telescope".to_string(), cost: 0.0 });
    grammar.add_lexical_rule(LexicalRule { lhs_id: v, rhs: "saw".to_string(), cost: 0.0 });
    grammar.add_lexical_rule(LexicalRule { lhs_id: v, rhs: "ran".to_string(), cost: 0.0 });
    grammar.add_lexical_rule(LexicalRule { lhs_id: p, rhs: "with".to_string(), cost: 0.0 });

    // Binary Rules (costs are -ln(prob))
    grammar.add_binary_rule(BinaryRule { lhs_id: s, rhs1_id: np, rhs2_id: vp, cost: -1.0_f64.ln() }); // P=1.0
    grammar.add_binary_rule(BinaryRule { lhs_id: np, rhs1_id: dt, rhs2_id: nn, cost: -1.0_f64.ln() }); // P=1.0
    grammar.add_binary_rule(BinaryRule { lhs_id: vp, rhs1_id: v, rhs2_id: np, cost: -0.7_f64.ln() });  // P=0.7 -> higher cost
    grammar.add_binary_rule(BinaryRule { lhs_id: vp, rhs1_id: vp, rhs2_id: pp, cost: -0.5_f64.ln() }); // P=0.5 -> lower cost
    grammar.add_binary_rule(BinaryRule { lhs_id: np, rhs1_id: np, rhs2_id: pp, cost: -0.2_f64.ln() }); // P=0.2 -> higher cost
    grammar.add_binary_rule(BinaryRule { lhs_id: pp, rhs1_id: p, rhs2_id: np, cost: -1.0_f64.ln() }); // P=1.0

    // Unary Rules
    grammar.add_unary_rule(UnaryRule { lhs_id: vp, rhs_id: v, cost: -0.1_f64.ln() }); // P=0.1

    grammar
}


// --- Tests for CYK parsing ---
#[test]
fn cyk_parse_simple_sentence() {
    let mut grammar = setup_test_grammar();
    // Simplify grammar for this test to force one parse
    let vp_id = grammar.get_or_intern_non_terminal("VP");
    let pp_id = grammar.get_or_intern_non_terminal("PP");
    let np_id = grammar.get_or_intern_non_terminal("NP");
    grammar.binary_rules_by_children.retain(|_k, v| {
        let rule = &v[0];
        (rule.lhs_id != vp_id || rule.rhs2_id != pp_id) &&
        (rule.lhs_id != np_id || rule.rhs2_id != pp_id)
    });
    let v_id = grammar.non_terminal_to_id["V"];
    grammar.unary_rules_by_rhs.get_mut(&v_id).unwrap()[0].cost = 0.0; // Make VP -> V cheap


    let sentence: Vec<String> = vec!["the".to_string(), "dog".to_string(), "ran".to_string()];
    let expected_tree_str = "(S (NP (DT the) (NN dog)) (VP (V ran)))";

    let result_node = parse_sentence(&grammar, &sentence, "S").unwrap();
    assert_eq!(tree_to_string(&result_node), expected_tree_str);
}


#[test]
fn cyk_parse_longer_sentence_ambiguous() {
     let grammar = setup_test_grammar();
     let sentence: Vec<String> = vec!["the".to_string(), "man".to_string(), "saw".to_string(), "a".to_string(), "dog".to_string(), "with".to_string(), "a".to_string(), "telescope".to_string()];
     let result_node = parse_sentence(&grammar, &sentence, "S").unwrap();
     // VP attachment has lower cost (-ln(0.5)) than NP attachment (-ln(0.2)), so it should be preferred.
     let expected_tree_vp_attach = "(S (NP (DT the) (NN man)) (VP (VP (V saw) (NP (DT a) (NN dog))) (PP (P with) (NP (DT a) (NN telescope)))))";
     assert_eq!(tree_to_string(&result_node), expected_tree_vp_attach);
}


#[test]
fn cyk_parse_no_parse() {
    let grammar = setup_test_grammar();
    let sentence = vec!["the".to_string(), "cat".to_string(), "barked".to_string()];
    let result = parse_sentence(&grammar, &sentence, "S");
    assert!(result.is_none());
}

#[test]
fn cyk_parse_empty_sentence() {
    let grammar = setup_test_grammar();
    let sentence: Vec<String> = vec![];
    let result = parse_sentence(&grammar, &sentence, "S");
    assert!(result.is_none());
}

// --- Tests for Transformations (Debinarise, Unk) ---

#[test]
fn test_debinarise_simple() {
    let binarized_str = "(S (NP (DT the) (NN|JJ (JJ big) (NN dog))) (VP|V (V ran)))";
    let binarized_tree = parse_tree(binarized_str).unwrap();
    let debinarised_tree = debinarise_node(binarized_tree);
    let expected_str = "(S (NP (DT the) (JJ big) (NN dog)) (V ran))";
    assert_eq!(tree_to_string(&debinarised_tree), expected_str);
}

#[test]
fn test_debinarise_no_op() {
    let original_str = "(S (NP (DT the) (NN dog)) (VP (V ran)))";
    let original_tree = parse_tree(original_str).unwrap();
    let debinarised_tree = debinarise_node(original_tree.clone());
    assert_eq!(debinarised_tree, original_tree);
}

#[test]
fn test_corpus_unking() {
    let mut tree1 = parse_tree("(S (A a) (B b))").unwrap();
    let mut tree2 = parse_tree("(S (C c) (B b))").unwrap();
    let mut tree3 = parse_tree("(S (A a) (D d))").unwrap();

    let mut word_counts = HashMap::new();
    let trees = vec![tree1.clone(), tree2.clone(), tree3.clone()];
    for t in &trees {
        let mut leaves = Vec::new();
        collect_leaves(t, &mut leaves);
        for leaf in leaves {
             *word_counts.entry(leaf.label.clone()).or_insert(0) += 1;
        }
    }

    // counts: a:2, b:2, c:1, d:1
    // threshold 1 should unk c and d
    replace_rare_words(&mut tree1, &word_counts, 1);
    replace_rare_words(&mut tree2, &word_counts, 1);
    replace_rare_words(&mut tree3, &word_counts, 1);

    assert_eq!(tree_to_string(&tree1), "(S (A a) (B b))");
    assert_eq!(tree_to_string(&tree2), "(S (C UNK) (B b))");
    assert_eq!(tree_to_string(&tree3), "(S (A a) (D UNK))");
}

#[test]
fn test_parser_unking_and_word_restoration() {
    let mut grammar = setup_test_grammar();
    // Add UNK to grammar
    let nn_id = grammar.get_or_intern_non_terminal("NN");
    grammar.terminals.insert("UNK".to_string());
    grammar.add_lexical_rule(LexicalRule { lhs_id: nn_id, rhs: "UNK".to_string(), cost: -0.1_f64.ln() });

    // "the" and "ran" are in grammar, "unicorn" is not.
    let sentence = vec!["the".to_string(), "unicorn".to_string(), "ran".to_string()];
    let original_words = sentence.clone();
    let mut words_for_parser = sentence.clone();

    // Emulate the --unking logic from main
    for word in &mut words_for_parser {
        if !grammar.terminals.contains(word) {
            *word = "UNK".to_string();
        }
    }
    assert_eq!(words_for_parser, vec!["the", "UNK", "ran"]);

    // The logic is now inside the main function, but we can test the components.
    // 1. Parse with "UNK"
    let mut result_tree = parse_sentence(&grammar, &words_for_parser, "S").unwrap();
    let unked_tree_str = tree_to_string(&result_tree);
    // Check that the parse tree contains UNK
    assert!(unked_tree_str.contains("(NN UNK)"));

    // 2. Restore words
    restore_words(&mut result_tree, &original_words);
    let final_tree_str = tree_to_string(&result_tree);
    let expected_str = "(S (NP (DT the) (NN unicorn)) (VP (V ran)))";
    assert_eq!(final_tree_str, expected_str);
}