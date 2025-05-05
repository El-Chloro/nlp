use std::iter::Peekable;
use std::str::Chars;

use crate::structs::{Node, ParseError};

// --- Tree Parsing  ---

pub fn parse_tree(input: &str) -> Result<Node, ParseError> {
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