use proc_macro::{Delimiter, Group, Ident, Literal, TokenStream, TokenTree};

use std::boxed::Box;
use std::cmp::Ordering;
use std::compile_error;

#[derive(Debug, Clone)]
struct Var {
    ident: Ident,
    name: String,
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
    Var(Var),     // free variable (witness)
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Operator {
    Mul,
    Add,
    Sub,
}

impl Operator {
    fn as_str(&self) -> &str {
        match self {
            Operator::Mul => "*",
            Operator::Add => "+",
            Operator::Sub => "-",
        }
    }
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
enum C {
    A,
    B,
    C,
    AB,
    CST,
}

#[derive(Debug)]
struct Coeff {
    coeff: Vec<C>, // constant
}

impl From<Vec<C>> for Coeff {
    fn from(coeff: Vec<C>) -> Self {
        assert!(coeff.len() >= 1);
        assert!(coeff.len() <= 5);
        Coeff { coeff }
    }
}

impl Coeff {
    fn len(&self) -> usize {
        self.coeff.len()
    }

    fn index(&self, t: C) -> Option<usize> {
        self.coeff.iter().copied().position(|v| v == t)
    }

    fn a(&self) -> Option<usize> {
        self.index(C::A)
    }

    fn b(&self) -> Option<usize> {
        self.index(C::B)
    }

    fn c(&self) -> Option<usize> {
        self.index(C::C)
    }

    fn cst(&self) -> Option<usize> {
        self.index(C::CST)
    }

    fn ab(&self) -> Option<usize> {
        self.index(C::AB)
    }
}

fn mul(l: Option<usize>, r: Option<usize>) -> Option<String> {
    Some(format!("{{ e1.{} * e2.{} }}", l?, r?))
}

fn sub(t1: Option<usize>, t2: Option<usize>) -> Option<String> {
    match (t1, t2) {
        (Some(v1), Some(v2)) => Some(format!("e1.{} - e2.{}", v1, v2)),
        (Some(v1), None) => Some(format!("e1.{}", v1)),
        (None, Some(v2)) => Some(format!("-e2.{}", v2)),
        _ => None,
    }
}

fn add(t1: Option<usize>, t2: Option<usize>) -> Option<String> {
    match (t1, t2) {
        (Some(v1), Some(v2)) => Some(format!("e1.{} + e2.{}", v1, v2)),
        (Some(v1), None) => Some(format!("e1.{}", v1)),
        (None, Some(v2)) => Some(format!("e2.{}", v2)),
        _ => None,
    }
}

fn add_seq(t: &[Option<String>]) -> Option<String> {
    let mut terms = t
        .iter()
        .filter(|v| v.is_some())
        .map(|v| v.as_ref().unwrap());

    let mut sum = terms.next()?.clone();

    for ti in terms {
        sum.push_str(" + ");
        sum.push_str(&ti);
    }

    Some(sum)
}

fn to_coeff(terms: Vec<(C, Option<String>)>) -> (Coeff, String) {
    let (coeff, sums): (Vec<C>, Vec<String>) = terms
        .into_iter()
        .filter(|(_, sum)| sum.is_some())
        .map(|(name, sum)| (name, sum.unwrap()))
        .unzip();

    let coeff = Coeff::from(coeff);

    let mut tuple = String::new();

    // compute terms
    tuple.push_str("{");
    for (i, sum) in sums.iter().enumerate() {
        tuple.push_str(&format!("let t{} = {};", i, sum));
    }

    // return tuple
    tuple.push_str("(t0,");
    for i in 1..coeff.len() {
        tuple.push_str(&format!("t{},", i));
    }
    tuple.push_str(")}");

    (coeff, tuple)
}

impl Expr {
    fn compile(&self, assignment: &[Var]) -> (Coeff, String) {
        match self {
            Expr::Const(literal) => (
                Coeff::from(vec![C::CST]),
                format!("({},)", literal.to_string()),
            ),

            Expr::Field(name) => (
                Coeff::from(vec![C::CST]),
                format!("({},)", name.to_string()),
            ),

            Expr::Var(var) => {
                let idx = assignment.iter().position(|v| v == var).unwrap();

                let term = match idx {
                    0 => C::A,
                    1 => C::B,
                    2 => C::C,
                    _ => unreachable!(),
                };

                (Coeff::from(vec![term]), format!("(F::one(),)"))
            }
            Expr::Op(op, expr1, expr2) => {
                let (c1, e1) = expr1.compile(assignment);
                let (c2, e2) = expr2.compile(assignment);

                let terms = match op {
                    Operator::Mul => vec![
                        (
                            C::A,
                            add_seq(&[mul(c1.a(), c2.cst()), mul(c2.a(), c1.cst())]),
                        ),
                        (
                            C::B,
                            add_seq(&[mul(c1.b(), c2.cst()), mul(c2.b(), c1.cst())]),
                        ),
                        (
                            C::C,
                            add_seq(&[mul(c1.c(), c2.cst()), mul(c2.c(), c1.cst())]),
                        ),
                        (
                            C::AB,
                            add_seq(&[
                                mul(c2.cst(), c1.ab()),
                                mul(c2.cst(), c2.ab()),
                                mul(c1.a(), c2.b()),
                                mul(c2.a(), c1.b()),
                            ]),
                        ),
                        (C::CST, mul(c1.cst(), c2.cst())),
                    ],
                    Operator::Add => vec![
                        (C::A, add(c1.a(), c2.a())),
                        (C::B, add(c1.b(), c2.b())),
                        (C::C, add(c1.c(), c2.c())),
                        (C::AB, add(c1.ab(), c2.ab())),
                        (C::CST, add(c1.cst(), c2.cst())),
                    ],
                    Operator::Sub => vec![
                        (C::A, sub(c1.a(), c2.a())),
                        (C::B, sub(c1.b(), c2.b())),
                        (C::C, sub(c1.c(), c2.c())),
                        (C::AB, sub(c1.ab(), c2.ab())),
                        (C::CST, sub(c1.cst(), c2.cst())),
                    ],
                };

                let (coeff, tuple) = to_coeff(terms);

                (
                    coeff,
                    format!("{{ let e1 = {}; let e2 = {}; {} }}", e1, e2, tuple),
                )
            }
        }
    }

    // checks (at compile time) that the expr
    // can be implemnted using a generic gate,
    // i.e. it does not have too high degree.
    //
    // And figures out the assignment of a,b,c.
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
                Expr::Var(_) => None,
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
                                return ml;
                            }
                            if ml.is_none() {
                                return mr;
                            }
                            if mr.is_none() {
                                return ml;
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
        let assigment = match check_muls(self) {
            Some(mul) => {
                // assign a and b
                let mut assigment = vec![];
                assigment.extend(mul);

                // find c variable
                if vars.len() > assigment.len() {
                    for var in vars.iter() {
                        if !assigment.contains(var) {
                            assigment.push(var.clone())
                        }
                    }
                }

                assert!(assigment.len() <= 3);
                assigment
            }
            None => vars,
        };

        assigment
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
        TokenTree::Literal(literal) => Some(Expr::Const(literal)),
        _ => None,
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
            splits.push(&tokens[j..i - CONS_EQ + 1]);
            j = i + 1;
            cons_eq = 0;
        }
    }

    splits.push(&tokens[j..]);

    assert_eq!(splits.len(), 2);

    let left = parse_expr(vars, TokenStream::from_iter(splits[0].iter().cloned()))?;
    let right = parse_expr(vars, TokenStream::from_iter(splits[1].iter().cloned()))?;

    return Some(Expr::Op(Operator::Sub, Box::new(left), Box::new(right)));
}

fn parse_op(o: TokenTree) -> Option<Operator> {
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
        Operator::Sub,
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
            break;
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
        let vars: Vec<Var> = vars
            .into_iter()
            .map(|v| match v {
                TokenTree::Ident(ident) => ident.into(),
                _ => panic!("variables must be identifiers, not {:?}", v),
            })
            .collect();

        // check length
        if vars.len() == 0 || vars.len() > 3 {
            panic!("generic gate must have between 1-3 variables");
        }

        return vars;
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
        _ => None,
    }
}

fn group<I: Iterator<Item = TokenTree>>(stream: &mut I) -> Option<Group> {
    match stream.next()? {
        TokenTree::Group(group) => Some(group),
        _ => None,
    }
}

fn seperator<I: Iterator<Item = TokenTree>>(stream: &mut I, sep: char) -> Result<(), &str> {
    match punct(stream) {
        Some(sep) => Ok(()),
        _ => Err("invalid/missing seperator"),
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
    let assignment = expr.compute_assigment();

    // compile expression for computing coefficients
    let (coeff, e) = expr.compile(&assignment[..]);

    // convert to generic gate
    let mut prog = String::new();

    prog.push_str("{\n");
    prog.push_str("let mut c = vec![F::zero(); GENERIC_ROW_COEFFS];\n");

    // coefficient vector
    prog.push_str(&format!("let e = {};\n", e));

    coeff
        .index(C::A)
        .map(|i| prog.push_str(&format!("c[0] = e.{}; // a\n", i)));

    coeff
        .index(C::B)
        .map(|i| prog.push_str(&format!("c[1] = e.{}; // b\n", i)));

    coeff
        .index(C::C)
        .map(|i| prog.push_str(&format!("c[2] = e.{}; // c\n", i)));

    coeff
        .index(C::AB)
        .map(|i| prog.push_str(&format!("c[3] = e.{}; // ab\n", i)));

    coeff
        .index(C::CST)
        .map(|i| prog.push_str(&format!("c[4] = e.{}; // const\n", i)));

    // witness array
    prog.push_str("let row = array_init(|i| {\n");
    prog.push_str("    match i { \n");
    for (i, var) in assignment.iter().enumerate() {
        prog.push_str(&format!("        {} => {},\n", i, var.name));
    }
    prog.push_str(&format!(
        "        _ => {}.var(|| F::zero()),\n",
        cs.to_string()
    ));
    prog.push_str("    }\n");
    prog.push_str("});\n");

    // add generic gate
    prog.push_str(&format!("{}.gate(GateSpec {{\n", cs.to_string()));
    prog.push_str("    typ: GateType::Generic,\n");
    prog.push_str("    row,\n");
    prog.push_str("    c,\n");
    prog.push_str("});\n");

    prog.push_str("}");

    // convert to token stream
    prog.parse().unwrap()
}
