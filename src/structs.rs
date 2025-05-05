use clap::Parser; 
use std::vec::Vec; 
// --- Data Structures ---

#[derive(Debug, Clone, PartialEq)]
pub struct Node { 
    pub label: String, 
    pub children: Vec<Node>,
}

impl Node {
    pub fn is_terminal(&self) -> bool { 
        self.children.is_empty()
    }
}

#[derive(Debug)]
pub struct ParseError(pub String); 

#[derive(Parser, Debug)]
#[command(name = "pcfg_tool", about = "Tools for PCFG-based parsing of natural language sentences", version)]
pub struct Cli { 
    #[command(subcommand)]
    pub command: Commands, 
}

#[derive(clap::Subcommand, Debug)]
pub enum Commands { 
    Induce(InduceArgs),
}

#[derive(Parser, Debug)]
pub struct InduceArgs { 
    #[arg()]
    pub grammar_output_prefix: Option<String>,
}