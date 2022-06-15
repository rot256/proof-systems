
use proc_macro::{TokenStream, Ident, Literal, Delimiter, TokenTree, Group};

use std::boxed::Box;
use std::cmp::Ordering;
use std::compile_error;

use ark_ff::{PrimeField, FftField};


/*
fn is_var<F: PrimeField + FftField>(v: Var<F>) -> Var<F> {
    v
}
*/

#[derive(Debug, Clone)]
struct Var {
    ident: Ident,
    name: String
}

impl From<Ident> for Var {
    fn from(ident: Ident) -> Var {
        let name = ident.to_string();
        Var { ident, name }
    }
}

impl PartialOrd for Var {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for Var {}

impl Ord for Var {
    fn cmp(&self, other: &Self) -> Ordering {
        self.name.cmp(&other.name)
    }
}

#[derive(Debug)]
enum Expr {
    Op(Operator, Box<Expr>, Box<Expr>),
    Const(Literal),
    Field(Ident), // identifier which is a field element
    Var(Var) // free variable (witness)
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Operator {
    Mul,
    Add,
    Sub
}

impl Operator {
    fn as_str(&self) -> &str {
        match self {
            Operator::Mul => "*",
            Operator::Add => "+",
            Operator::Sub => "-"
        }
    }
}

impl Expr {
    // checks (at compile time) that the expr 
    // can be implemnted using a generic gate, 
    // i.e. it does not have too high degree.
    //
    // Because of this check we can compile to code which "could fail at run-time",
    // however because of this static analysis it cannot.
    fn compute_assigment(&self) -> Vec<Var> {
        let mut mul: Option<(Ident, Ident)> = None;
        
        fn variables(expr: &Expr) -> Vec<Var> {
            match expr {
                Expr::Var(var) => vec![var.clone()],
                Expr::Op(_, l, r) => {
                    let mut vars = variables(&l);
                    vars.append(&mut variables(&r));
                    vars.sort();
                    vars.dedup();
                    vars
                }
                _ => vec![],
            }
        }

        fn check_muls(expr: &Expr) -> Option<[Var; 2]> {
            match expr {
                Expr::Var(name) => None,
                Expr::Op(op, l, r) => {
                    let vl = variables(l);
                    let vr = variables(r);

                    let ml = check_muls(l);
                    let mr = check_muls(r);

                    match op {
                        Operator::Mul => {
                            match (vl.len(), vr.len(), ml, mr) {
                                // exactly one var on both sides of the mul
                                (1, 1, None, None) => {
                                    let mut m = [vl[0].clone(), vr[0].clone()];
                                    m.sort();
                                    Some(m)
                                }
                                // mul by constant
                                (0, _, None, m) => m,
                                (_, 0, m, None) => m,
                                // multiple vars on either side
                                _ => {
                                    panic!("generic gate has too high multiplicative degree")
                                }
                            }
                        }
                        // linear operator: check that we dont 
                        // have multiple distinct multiplications
                        _ => {
                            if ml == mr {
                                return ml
                            }
                            if ml.is_none() {
                                return mr
                            }
                            if mr.is_none() {
                                return ml
                            }
                            // both Some and not the same :(
                            panic!("more than 1 distinct multiplication")
                        }
                    }   
                }
                _ => None,
            }
        }

        // 
        let vars = variables(self);

        // figure out which variables corresponds to a,b,c
        let ass = match check_muls(self) {
            Some(mul) => {
                // assign a and b
                let mut ass = vec![];
                ass.extend(mul);

                // find c variable
                if vars.len() > ass.len() {
                    for var in vars.iter() {
                        if !ass.contains(var) {
                            ass.push(var.clone())
                        }
                    }
                }

                assert!(ass.len() <= 3);
                ass
            }
            None => vars
        };

        println!("assignment = {:?}", ass);

        ass
    }

    // flattens an expression which should be zero
    fn render(self) -> String {
        println!("{:?}", self);

        match self {
            Expr::Op(op, expr1, expr2) => {
                println!("op = {:?} {}", op, op.as_str());
                format!(
                    "{{ let expr1 = {}; let expr2 = {}; expr1 {} expr2}}",
                    expr1.render(),
                    expr2.render(),
                    op.as_str()
                )
            }
            Expr::Field(ident) => {
                format!(
                    "{{ GenericExpr::from_constant({})}}", 
                    ident.to_string()
                )
            }
            Expr::Var(var) => {
                format!(
                    "{{ GenericExpr::from_var({}) }}",
                    var.name
                )
            }
            Expr::Const(val) => {
                format!(
                    "{{ GenericExpr::from_constant({}) }}",
                    val.to_string()
                )
            }
            _ => unimplemented!()
        }
    }
}

fn parse_term(vars: &[Var], e: TokenTree) -> Option<Expr> {  
    match e {
        TokenTree::Group(sub_expr) => {
            assert_eq!(sub_expr.delimiter(), Delimiter::Parenthesis);
            parse_expr(vars, sub_expr.stream())
        }
        TokenTree::Ident(ident) => {
            let var = Var::from(ident);
            if vars.contains(&var) {
                Some(Expr::Var(var))
            } else {
                Some(Expr::Field(var.ident))
            }
        }
        TokenTree::Literal(literal) => {
            Some(Expr::Const(literal))
        }
        _ => None
    }
} 

const EQ: char = '=';
const CONS_EQ: usize = 2;

fn parse_top(vars: &[Var], expr: Group) -> Option<Expr> {
    let tokens: Vec<TokenTree> = expr.stream().into_iter().collect();

    let mut splits: Vec<&[TokenTree]> = vec![];

    // find equality
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
            splits.push(&tokens[j..i-CONS_EQ+1]);
            j = i+1;
            cons_eq = 0;
        }
    }

    splits.push(&tokens[j..]);

    println!("{:#?}", splits);

    assert_eq!(splits.len(), 2);

    let left = parse_expr(vars, TokenStream::from_iter(splits[0].iter().cloned()))?;
    let right = parse_expr(vars, TokenStream::from_iter(splits[1].iter().cloned()))?;

    return Some(Expr::Op(Operator::Sub, Box::new(left), Box::new(right)));
}


fn parse_op(o: TokenTree) -> Option<Operator> {
    match o {
        TokenTree::Punct(op) => {
            match op.as_char() {
                '*' => Some(Operator::Mul),
                '+' => Some(Operator::Add),
                '-' => Some(Operator::Sub),
                _ => panic!("Unexpected operator")
            }
        }
        _ => None
    }
}

// Parses the generic gate expression into a generic gate
fn parse_expr(vars: &[Var], expr: TokenStream) -> Option<Expr> {
    let mut ops: Vec<Operator> = vec![];
    let mut terms: Vec<Expr> = vec![];
    let mut is_term: bool = true;
 
    for token in expr.into_iter() {
        // parse term or operator
        if is_term {
            terms.push(parse_term(vars, token)?);
        } else {
            ops.push(parse_op(token)?);
        }

        // alternating between terms and operators
        is_term = !is_term;
    }

    // we should finish with a term
    assert_eq!(is_term, false);

    // 
    let prec = vec![
        Operator::Mul, // binds tightest
        Operator::Add,
        Operator::Sub
    ];

    // repeatedly coalesce terms
    // this is not very efficient, however the formulas are VERY SMALL.
    for op in prec {
        // coalesce one application of op at a time
        'coalesce: loop {
            assert_eq!(terms.len() - 1, ops.len());
            for i in 0..ops.len() {
                if ops[i] == op {
                    ops.remove(i);
                    let t1 = terms.remove(i);
                    let t2 = terms.remove(i);
                    terms.insert(i, Expr::Op(op, Box::new(t1), Box::new(t2)));
                    continue 'coalesce;
                }
            }
            break
        }
    }

    // there should be exactly one term left
    assert_eq!(terms.len(), 1);
    terms.pop()
}

fn parse_list(stream: TokenStream) -> Option<(Vec<TokenTree>, Vec<char>)> {
    let mut seps = vec![];
    let mut terms: Vec<TokenTree> = vec![];
    let mut stream = stream.into_iter();

    // parse non-empty list
    terms.push(token(&mut stream)?);
    while let Some(sep) = punct(&mut stream) {
        seps.push(sep);
        terms.push(token(&mut stream)?);
    }

    Some((terms, seps))
}

fn parse_vars(token: TokenTree) -> Vec<Var> {
    if let TokenTree::Group(group) = token {
        // split list on ,
        let (vars, sep) = parse_list(group.stream()).expect("variables must be seperated by ,");
        assert!(sep.into_iter().all(|c| c == ','));

        // parse as literals
        let vars: Vec<Var> = vars.into_iter().map(|v| {
            match v {
                TokenTree::Ident(ident) => ident.into(),
                _ => panic!("variables must be identifiers, not {:?}", v),
            }
        }).collect();

        // check length
        if vars.len() == 0 || vars.len() > 3 {
            panic!("generic gate must have between 1-3 variables");
        }

        return vars
    } else {
        panic!("variables must be a tuple");
    }

}

fn token<I: Iterator<Item = TokenTree>>(stream: &mut I) -> Option<TokenTree> {
    stream.next()
}

fn punct<I: Iterator<Item = TokenTree>>(stream: &mut I) -> Option<char> {
    match stream.next()? {
        TokenTree::Punct(punct) => Some(punct.as_char()),
        _ => None
    }
}

fn group<I: Iterator<Item = TokenTree>>(stream: &mut I) -> Option<Group> {
    match stream.next()? {
        TokenTree::Group(group) => Some(group),
        _ => None
    }
}

fn seperator<I: Iterator<Item = TokenTree>>(stream: &mut I, sep: char) -> Result<(), &str> {
    match punct(stream) {
        Some(sep) => Ok(()),
        _ => Err("invalid/missing seperator")
    }
}

fn end<I: Iterator<Item = TokenTree>>(stream: &mut I, sep: char) -> Result<(), &str> {
    match token(stream) {
        Some(_) => Err("expected end of stream"),
        None => Ok(())
    }
}

/// Transforms a generic assert into a generic gate
#[proc_macro]
pub fn generic(input: TokenStream) -> TokenStream {
    //let mut args = vec![];

    let mut args = input.into_iter();

    let cs = token(&mut args).expect("cs missing");
    
    seperator(&mut args, ',').unwrap();

    let vars = parse_vars(token(&mut args).expect("variable failed to parse"));

    seperator(&mut args, ':').unwrap();

    let expr = parse_top(&vars, group(&mut args).expect("expected group")).unwrap();

    // check that the constraints can be enforced using a generic gate
    let ass = expr.compute_assigment();

    // convert to TokenStream
    let expr = expr.render();

    // enforce the expr (should be 0)
    let path = "crate";
    let prog = format!(
        "{{ use {}::GenericExpr; let expr0 = {}; expr0.enforce({}) }}",
        path,
        expr,
        cs
    );

    println!("{}", prog);

    // convert to token stream
    prog.parse().unwrap()
}