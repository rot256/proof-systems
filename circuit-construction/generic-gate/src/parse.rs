
use proc_macro::{Delimiter, Group, Ident, Literal, TokenStream, TokenTree};

use std::collections::HashMap;

use crate::types::{Var, Expr, Operator, Const, Vars};

const EQ: char = '=';
const CONS_EQ: usize = 2;
const FREE_VAR: char = '?';

fn parse_list(stream: TokenStream) -> Option<(Vec<TokenTree>, Vec<char>)> {
    let mut seps = vec![];
    let mut terms: Vec<TokenTree> = vec![];
    let mut stream = stream.into_iter();

    // parse non-empty list
    terms.push(stream.next()?);
    while let Some(sep) = punct(&mut stream) {
        seps.push(sep);
        terms.push(stream.next()?);
    }

    Some((terms, seps))
}

fn punct<I: Iterator<Item = TokenTree>>(stream: &mut I) -> Option<char> {
    match stream.next()? {
        TokenTree::Punct(punct) => Some(punct.as_char()),
        _ => None,
    }
}

pub fn group<I: Iterator<Item = TokenTree>>(stream: &mut I) -> Option<Group> {
    match stream.next()? {
        TokenTree::Group(group) => Some(group),
        _ => None,
    }
}

pub fn seperator<I: Iterator<Item = TokenTree>>(stream: &mut I, sep: char) -> Result<(), &str> {
    match punct(stream) {
        Some(sep) => Ok(()),
        _ => Err("invalid/missing seperator"),
    }
}

impl Var {
    fn parse(vars: &Vars, v: TokenTree) -> Option<Self> {
        match v {
            TokenTree::Punct(punct) => {
                match punct.as_char() {
                    FREE_VAR => Some(Var::Free),
                    _ => None
                }
            }
            TokenTree::Ident(ident) => vars.var(&ident.to_string()),
            _ => None
        }
    }
}

impl Operator {
    pub fn parse(o: TokenTree) -> Option<Operator> {
        match o {
            TokenTree::Punct(op) => match op.as_char() {
                '*' => Some(Operator::Mul),
                '+' => Some(Operator::Add),
                '-' => Some(Operator::Sub),
                _ => panic!("unexpected operator {}", op),
            },
            _ => None,
        }
    }
}

// A list of <expr> (op) <expr> (op) ... (op) <expr>
struct ExprList {
    ops: Vec<Operator>,
    exprs: Vec<Expr>
}

impl ExprList {
    fn parse(vars: &Vars, stream: TokenStream) -> Option<Self> {
        let mut ops: Vec<Operator> = vec![];
        let mut exprs: Vec<Expr> = vec![];
       
        for (i, token) in stream.into_iter().enumerate() {
            if i % 2 == 0 {
                exprs.push(Expr::parse(vars, token)?)
            } else {
                ops.push(Operator::parse(token)?)
            }
        }

        assert_eq!(ops.len() + 1, exprs.len());

        Some(
            ExprList{
                ops,
                exprs
            }
        )
    }

    fn to_expr(self) -> Expr {
        //
        let prec = vec![
            Operator::Mul, // binds tightest
            Operator::Add,
            Operator::Sub,
        ];

        let mut ops = self.ops;
        let mut exprs = self.exprs;

        // repeatedly coalesce terms
        // this is not very efficient, however the formulas are VERY SMALL.
        for op in prec {
            // coalesce one application of op at a time
            'coalesce: loop {
                assert_eq!(exprs.len() - 1, ops.len());
                for i in 0..ops.len() {
                    if ops[i] == op {
                        ops.remove(i);
                        let t1 = exprs.remove(i);
                        let t2 = exprs.remove(i);
                        exprs.insert(i, Expr::Op(op, Box::new(t1), Box::new(t2)));
                        continue 'coalesce;
                    }
                }
                break;
            }
        }

        // there should be exactly one expr left
        assert_eq!(exprs.len(), 1);
        assert_eq!(ops.len(), 0);
        exprs.pop().unwrap()
    } 
}

impl Const {
    fn parse(vars: &Vars, c: TokenTree) -> Option<Const> {
        match c {
            TokenTree::Ident(ident) => Some(Const::Ident(ident)),
            TokenTree::Literal(literal) => Some(Const::Literal(literal)),
            _ => None
        }
    }
}

impl Expr {
    pub fn parse(vars: &Vars, e: TokenTree) -> Option<Expr> {
        match e {
            TokenTree::Group(sub) => {
                assert_eq!(sub.delimiter(), Delimiter::Parenthesis);
                let list = ExprList::parse(vars, sub.stream())?;
                Some(list.to_expr())
            }
            // could be constant or variable
            TokenTree::Ident(_) | TokenTree::Punct(_) => {
                if let Some(var) = Var::parse(vars, e.clone()) {
                    Some(Expr::Var(var))
                } else {
                    let constant = Const::parse(vars, e)?;
                    Some(Expr::Const(constant))
                }
            }
            // must be constant
            TokenTree::Literal(_) => {
                let constant = Const::parse(vars, e)?;
                Some(Expr::Const(constant))
            }
            _ => {
                panic!("invalid expr: {:?}", e);
            }
        }
    }

    pub fn parse_top(vars: &Vars, expr: Group) -> Option<Expr> {
        let tokens: Vec<TokenTree> = expr.stream().into_iter().collect();

        let mut splits: Vec<&[TokenTree]> = vec![];
    
        // find ==
        let mut j = 0;
        let mut cons_eq: usize = 0;
        for (i, token) in tokens.iter().enumerate() {
            if let TokenTree::Punct(punct) = token {
                if punct.as_char() == EQ {
                    cons_eq += 1;
                } else {
                    cons_eq = 0;
                }
            } else {
                cons_eq = 0;
            }
    
            // check if we should split
            if cons_eq == CONS_EQ {
                splits.push(&tokens[j..i - CONS_EQ + 1]);
                j = i + 1;
                cons_eq = 0;
            }
        }
    
        splits.push(&tokens[j..]);
    
        assert_eq!(splits.len(), 2);

    
        // parse left/right side
    
        let left = ExprList::parse(
            vars, 
            TokenStream::from_iter(splits[0].iter().cloned())
        )?;
        
        let right = ExprList::parse(
            vars, 
            TokenStream::from_iter(splits[1].iter().cloned())
        )?;
    
        // subtract right from left
        return Some(
            Expr::Op(
                Operator::Sub, 
                Box::new(left.to_expr()), 
                Box::new(right.to_expr())
            )
        );
    }
}

impl Vars {
    pub fn parse(list: TokenTree) -> Self {
        match list {
            TokenTree::Group(group) => {
                // split list on ,
                let (vars, sep) = parse_list(group.stream()).expect("variables must be seperated by ,");
                assert!(sep.into_iter().all(|c| c == ','));

                // assign the names to V1, V2, V3
                let names = vars.into_iter().map(|v| match v {
                    TokenTree::Ident(ident) =>ident.to_string(), 
                    _ => panic!("variables must be identifiers, not {:?}", v),
                });

                Vars::new(names)
            }
            _ => panic!("variables must be a tuple")
        }
    }
}
