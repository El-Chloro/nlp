use clap::{Parser, Subcommand, Args}; 
use std::path::PathBuf; 
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

#[derive(Subcommand, Debug)]
pub enum Commands { 
    Induce(InduceArgs),
    Parse(ParseArgs),
}

#[derive(Args, Debug)]
pub struct InduceArgs { 
    #[arg()]
    pub grammar_output_prefix: Option<String>,
}

#[derive(Args, Debug)] 
pub struct ParseArgs {
    #[arg(value_name = "RULES")]
    pub rules_file: PathBuf, 

    #[arg(value_name = "LEXICON")]
    pub lexicon_file: PathBuf,

    #[arg(short = 'p', long = "paradigm", value_name = "PARADIGM", default_value = "cyk")]
    pub paradigma: String, 

    #[arg(short = 'i', long = "initial-nonterminal", value_name = "N", default_value = "ROOT")]
    pub initial_nonterminal: String, 

    // --- Optional flags ---
    #[arg(short = 'u', long = "unking", default_value_t = false)]
    pub unking: bool,

    #[arg(short = 's', long = "smoothing", default_value_t = false)]
    pub smoothing: bool,

    #[arg(short = 't', long = "threshold-beam", value_name = "THRESHOLD")]
    pub threshold_beam: Option<f64>,

    #[arg(short = 'r', long = "rank-beam", value_name = "RANK")]
    pub rank_beam: Option<usize>,

    #[arg(short = 'a', long = "astar", value_name = "PATH")]
    pub astar_outside_weights_file: Option<PathBuf>,
}