//! [TinyExpr](https://github.com/kondrak/tinyexpr-rs) is a tiny recursive descent expression
//! parser, compiler, and evaluation engine for math expressions.
//! This is a work in progress port of [TinyExpr](https://github.com/codeplea/tinyexpr) to Rust.
//!
//! Current release only supports built-in system functions (trigonometry, algebraic operations, constants, etc.).
//! See the `tests` module for more examples.
//!
//!# Quick Start
//!
//!```
//!extern crate tinyexpr;
//!
//!fn main()
//!{
//!    // parse the expression and fetch result
//!    let r = tinyexpr::interp("2+2*2").unwrap();
//!
//!    // should print "6"
//!    println!("{:?}", r);
//!}
//!```
#[macro_use]
extern crate bitflags;
extern crate phf;
extern crate rand;
pub mod error;
use error::Result;
use phf::phf_map;
use rand::prelude::*;
use std::f64::consts;
use std::str::FromStr;

#[doc(hidden)]
bitflags! {
    #[doc(hidden)]
    pub struct Flags: u64 {
        const TE_VARIABLE  = 0;
        const TE_CONSTANT  = 1;
        const TE_FUNCTION0 = 8;
        const TE_FUNCTION1 = 9;
        const TE_FUNCTION2 = 10;
        const TE_FUNCTION3 = 11;
        const TE_FUNCTION4 = 12;
        const TE_FUNCTION5 = 13;
        const TE_FUNCTION6 = 14;
        const TE_FUNCTION7 = 15;
        const TE_CLOSURE0  = 16;
        const TE_CLOSURE1  = 17;
        const TE_CLOSURE2  = 18;
        const TE_CLOSURE3  = 19;
        const TE_CLOSURE4  = 20;
        const TE_CLOSURE5  = 21;
        const TE_CLOSURE6  = 22;
        const TE_CLOSURE7  = 23;
        const TE_FLAG_PURE = 32;
        const TOK_NULL     = 24;
        const TOK_ERROR    = 25;
        const TOK_END      = 26;
        const TOK_SEP      = 27;
        const TOK_OPEN     = 28;
        const TOK_CLOSE    = 29;
        const TOK_NUMBER   = 30;
        const TOK_VARIABLE = 31;
        const TOK_INFIX    = 32;
        const T_MASK       = 0x0000001F;
    }
}

macro_rules! type_mask {
    ($x:expr) => {
        $x & Flags::T_MASK
    };
}

#[allow(unused_macros)]
macro_rules! is_pure {
    ($x:expr) => {
        ($x & Flags::TE_FLAG_PURE).bits() != 0
    };
}

#[allow(unused_macros)]
macro_rules! is_function {
    ($x:expr) => {
        ($x & Flags::TE_FUNCTION0).bits() != 0
    };
}

#[allow(unused_macros)]
macro_rules! is_closure {
    ($x:expr) => {
        ($x & Flags::TE_CLOSURE0).bits() != 0
    };
}

macro_rules! arity {
    ($x:expr) => {
        if ($x & (Flags::TE_FUNCTION0 | Flags::TE_CLOSURE0)).bits() != 0 {
            $x.bits() & 0x00000007
        } else {
            0
        }
    };
}

struct Functions {
    fun: fn(f64, f64) -> f64,
    flag: Flags,
}

impl Clone for Functions {
    fn clone(&self) -> Functions {
        Functions {
            fun: self.fun,
            flag: self.flag,
        }
    }
}

static FUNCTIONS: phf::Map<&'static str, Functions> = phf_map! {
    "abs" => Functions{fun: abs, flag: Flags::TE_FUNCTION1},
    "acos" => Functions{fun: acos, flag: Flags::TE_FUNCTION1},
    "asin" => Functions{fun: asin, flag: Flags::TE_FUNCTION1},
    "atan" => Functions{fun: atan, flag: Flags::TE_FUNCTION1},
    "atan2" => Functions{fun: atan2, flag: Flags::TE_FUNCTION2},
    "ceil" => Functions{fun: ceil, flag: Flags::TE_FUNCTION1},
    "cos" => Functions{fun: cos, flag: Flags::TE_FUNCTION1},
    "cosh" => Functions{fun: cosh, flag: Flags::TE_FUNCTION1},
    "e" => Functions{fun: e, flag: Flags::TE_FUNCTION0},
    "exp" => Functions{fun: exp, flag: Flags::TE_FUNCTION1},
    "floor" => Functions{fun: floor, flag: Flags::TE_FUNCTION1},
    "ln" => Functions{fun: ln, flag: Flags::TE_FUNCTION1},
    "log" => Functions{fun: log, flag: Flags::TE_FUNCTION1},
    "log10" => Functions{fun: log10, flag: Flags::TE_FUNCTION1},
    "pi" => Functions{fun: pi, flag: Flags::TE_FUNCTION0},
    "pow" => Functions{fun: pow, flag: Flags::TE_FUNCTION2},
    "rand01" => Functions{fun: rand01, flag: Flags::TE_FUNCTION0},
    "randint" => Functions{fun: randint, flag: Flags::TE_FUNCTION2},
    "round" => Functions{fun: round, flag: Flags::TE_FUNCTION1},
    "sin" => Functions{fun: sin, flag: Flags::TE_FUNCTION1},
    "sinh" => Functions{fun: sinh, flag: Flags::TE_FUNCTION1},
    "sqrt" => Functions{fun: sqrt, flag: Flags::TE_FUNCTION1},
    "tan" => Functions{fun: tan, flag: Flags::TE_FUNCTION1},
    "tanh" => Functions{fun: tanh, flag: Flags::TE_FUNCTION1},
};

fn dummy(_: f64, _: f64) -> f64 {
    panic!("called dummy!")
}
fn add(a: f64, b: f64) -> f64 {
    a + b
}
fn sub(a: f64, b: f64) -> f64 {
    a - b
}
fn mul(a: f64, b: f64) -> f64 {
    a * b
}
fn div(a: f64, b: f64) -> f64 {
    a / b
}
fn fmod(a: f64, b: f64) -> f64 {
    a % b
}
fn neg(a: f64, _: f64) -> f64 {
    -a
}
fn comma(_: f64, b: f64) -> f64 {
    b
}
fn abs(a: f64, _: f64) -> f64 {
    a.abs()
}
fn acos(a: f64, _: f64) -> f64 {
    a.acos()
}
fn asin(a: f64, _: f64) -> f64 {
    a.asin()
}
fn atan(a: f64, _: f64) -> f64 {
    a.atan()
}
fn atan2(a: f64, b: f64) -> f64 {
    a.atan2(b)
}
fn ceil(a: f64, _: f64) -> f64 {
    a.ceil()
}
fn cos(a: f64, _: f64) -> f64 {
    a.cos()
}
fn cosh(a: f64, _: f64) -> f64 {
    a.cosh()
}
fn e(_: f64, _: f64) -> f64 {
    consts::E
}
fn exp(a: f64, _: f64) -> f64 {
    a.exp()
}
fn floor(a: f64, _: f64) -> f64 {
    a.floor()
}
fn ln(a: f64, _: f64) -> f64 {
    a.ln()
}
fn log(a: f64, _: f64) -> f64 {
    a.log10()
}
fn log10(a: f64, _: f64) -> f64 {
    a.log10()
}
fn pi(_: f64, _: f64) -> f64 {
    consts::PI
}
fn pow(a: f64, b: f64) -> f64 {
    a.powf(b)
}
fn rand01(_: f64, _: f64) -> f64 {
    let mut rng = rand::thread_rng();
    rng.gen()
}
fn randint(a: f64, b: f64) -> f64 {
    let mut rng = rand::thread_rng();
    rng.gen_range(a, b).round()
}
fn round(a: f64, _: f64) -> f64 {
    a.round()
}
fn sin(a: f64, _: f64) -> f64 {
    a.sin()
}
fn sinh(a: f64, _: f64) -> f64 {
    a.sinh()
}
fn sqrt(a: f64, _: f64) -> f64 {
    a.sqrt()
}
fn tan(a: f64, _: f64) -> f64 {
    a.tan()
}
fn tanh(a: f64, _: f64) -> f64 {
    a.tanh()
}

#[doc(hidden)]
#[derive(Debug)]
pub struct Expr {
    pub e_type: Flags,
    pub value: f64,
    pub bound: i8,
    pub function: fn(f64, f64) -> f64,
    pub parameters: Vec<Expr>,
}

impl Expr {
    fn new() -> Expr {
        Expr {
            e_type: Flags::TOK_NULL,
            value: 0.0,
            bound: 0,
            function: dummy,
            parameters: Vec::<Expr>::new(),
        }
    }
}

impl Clone for Expr {
    fn clone(&self) -> Expr {
        Expr {
            e_type: self.e_type,
            value: self.value,
            bound: self.bound,
            function: self.function,
            parameters: self.parameters.clone(),
        }
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub struct Variable {
    pub name: String,
    pub address: i8,
    pub function: fn(f64, f64) -> f64,
    pub v_type: Flags,
    pub context: Vec<Expr>,
}

impl Variable {
    fn new(name: &str, v_type: Flags) -> Variable {
        Variable {
            name: String::from(name),
            address: 0,
            function: dummy,
            v_type: v_type,
            context: Vec::<Expr>::new(),
        }
    }
}

impl Clone for Variable {
    fn clone(&self) -> Variable {
        Variable {
            name: self.name.clone(),
            address: self.address,
            function: self.function,
            v_type: self.v_type,
            context: self.context.clone(),
        }
    }
}

#[derive(Debug)]
struct State {
    pub next: String,
    pub s_type: Flags,
    pub n_idx: usize,
    pub value: f64,
    pub bound: i8,
    pub function: fn(f64, f64) -> f64,
    pub context: Vec<Expr>,
    pub lookup: Vec<Variable>,
}

impl State {
    fn new(expression: &str) -> State {
        State {
            next: String::from(expression),
            s_type: Flags::TOK_NULL,
            n_idx: 0,
            value: 0.0,
            bound: 0,
            function: mul,
            context: Vec::<Expr>::new(),
            lookup: Vec::<Variable>::new(),
        }
    }
}

// todo
fn new_expr(e_type: Flags, params: Option<Vec<Expr>>) -> Expr {
    let _arity = arity!(e_type);
    let mut ret = Expr::new();

    ret.e_type = e_type;
    ret.bound = 0;
    if let Some(params) = params {
        ret.parameters = params;
    }

    ret
}

fn find_lookup(s: &State, txt: &str) -> Option<Variable> {
    for var in &s.lookup {
        if &(*var.name) == txt {
            return Some((*var).clone());
        }
    }

    None
}

fn find_builtin(txt: &str) -> Option<Variable> {
    match FUNCTIONS.get(txt) {
        Some(v) => {
            let mut var = Variable::new(txt, v.flag | Flags::TE_FLAG_PURE);
            var.function = v.fun;
            return Some(var);
        }
        None => None,
    }
}

fn next_token(s: &mut State) -> Result<String> {
    s.s_type = Flags::TOK_NULL;

    while s.s_type == Flags::TOK_NULL {
        if s.n_idx >= s.next.len() {
            s.s_type = Flags::TOK_END;
            break;
        }

        let next_char = s.next.as_bytes()[s.n_idx] as char;
        // try reading a number
        if (next_char >= '0' && next_char <= '9') || next_char == '.' {
            let mut num_str = String::new();
            let mut c = next_char;

            // extract the number part to separate string which we then convert to f64
            while (c >= '0' && c <= '9') || c == '.' {
                num_str.push(c);
                s.n_idx += 1;
                if s.n_idx < s.next.len() {
                    c = s.next.as_bytes()[s.n_idx] as char;
                } else {
                    break;
                }
            }
            s.value = f64::from_str(&num_str).unwrap();
            s.s_type = Flags::TOK_NUMBER;
        } else {
            // look for a variable or builting function call
            if next_char >= 'a' && next_char <= 'z' {
                let mut txt_str = String::new();
                let mut c = next_char;

                while (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') {
                    txt_str.push(c);
                    s.n_idx += 1;
                    if s.n_idx < s.next.len() {
                        c = s.next.as_bytes()[s.n_idx] as char;
                    } else {
                        break;
                    }
                }

                let mut var = find_lookup(&s, &txt_str);
                if let None = var {
                    var = find_builtin(&txt_str);
                }

                if let Some(v) = var {
                    match type_mask!(v.v_type) {
                        Flags::TE_VARIABLE => {
                            s.s_type = Flags::TOK_VARIABLE;
                            s.bound = v.address;
                        }
                        Flags::TE_CLOSURE0 => s.context = v.context,
                        Flags::TE_CLOSURE1 => s.context = v.context,
                        Flags::TE_CLOSURE2 => s.context = v.context,
                        Flags::TE_CLOSURE3 => s.context = v.context,
                        Flags::TE_CLOSURE4 => s.context = v.context,
                        Flags::TE_CLOSURE5 => s.context = v.context,
                        Flags::TE_CLOSURE6 => s.context = v.context,
                        Flags::TE_CLOSURE7 => s.context = v.context,
                        Flags::TE_FUNCTION0 => {
                            s.s_type = v.v_type;
                            s.function = v.function;
                        }
                        Flags::TE_FUNCTION1 => {
                            s.s_type = v.v_type;
                            s.function = v.function;
                        }
                        Flags::TE_FUNCTION2 => {
                            s.s_type = v.v_type;
                            s.function = v.function;
                        }
                        Flags::TE_FUNCTION3 => {
                            s.s_type = v.v_type;
                            s.function = v.function;
                        }
                        Flags::TE_FUNCTION4 => {
                            s.s_type = v.v_type;
                            s.function = v.function;
                        }
                        Flags::TE_FUNCTION5 => {
                            s.s_type = v.v_type;
                            s.function = v.function;
                        }
                        Flags::TE_FUNCTION6 => {
                            s.s_type = v.v_type;
                            s.function = v.function;
                        }
                        Flags::TE_FUNCTION7 => {
                            s.s_type = v.v_type;
                            s.function = v.function;
                        }
                        _ => {}
                    }
                } else {
                    s.s_type = Flags::TOK_ERROR;
                }
            } else {
                // look for an operator or special character
                match s.next.as_bytes()[s.n_idx] as char {
                    '+' => {
                        s.s_type = Flags::TOK_INFIX;
                        s.function = add;
                    }
                    '-' => {
                        s.s_type = Flags::TOK_INFIX;
                        s.function = sub;
                    }
                    '*' => {
                        s.s_type = Flags::TOK_INFIX;
                        s.function = mul;
                    }
                    '/' => {
                        s.s_type = Flags::TOK_INFIX;
                        s.function = div;
                    }
                    '^' => {
                        s.s_type = Flags::TOK_INFIX;
                        s.function = pow;
                    }
                    '%' => {
                        s.s_type = Flags::TOK_INFIX;
                        s.function = fmod;
                    }
                    '(' => s.s_type = Flags::TOK_OPEN,
                    ')' => s.s_type = Flags::TOK_CLOSE,
                    ',' => s.s_type = Flags::TOK_SEP,
                    ' ' | '\t' | '\n' | '\r' => {}
                    _ => s.s_type = Flags::TOK_ERROR,
                }
                s.n_idx += 1;
            }
        }
    }

    Ok(String::new())
}

fn base(s: &mut State) -> Result<Expr> {
    let mut ret: Expr;

    match type_mask!(s.s_type) {
        Flags::TOK_NUMBER => {
            ret = new_expr(Flags::TE_CONSTANT, None);
            ret.value = s.value;
            next_token(s).unwrap();
        }
        Flags::TOK_VARIABLE => {
            ret = new_expr(Flags::TE_VARIABLE, None);
            ret.bound = s.bound;
            next_token(s).unwrap();
        }
        Flags::TE_FUNCTION0 | Flags::TE_CLOSURE0 => {
            ret = new_expr(s.s_type, None);
            ret.function = s.function;

            next_token(s).unwrap();
            // todo: set parameters
        }
        Flags::TE_FUNCTION1 | Flags::TE_CLOSURE1 => {
            ret = new_expr(s.s_type, None);
            ret.function = s.function;
            // todo: set parameters
            next_token(s).unwrap();
            ret.parameters.push(power(s).unwrap());
            // todo: set parameters
        }
        Flags::TE_FUNCTION2
        | Flags::TE_CLOSURE2
        | Flags::TE_FUNCTION3
        | Flags::TE_CLOSURE3
        | Flags::TE_FUNCTION4
        | Flags::TE_CLOSURE4
        | Flags::TE_FUNCTION5
        | Flags::TE_CLOSURE5
        | Flags::TE_FUNCTION6
        | Flags::TE_CLOSURE6
        | Flags::TE_FUNCTION7
        | Flags::TE_CLOSURE7 => {
            let arity = arity!(s.s_type);

            ret = new_expr(s.s_type, None);
            ret.function = s.function;
            // todo: set parameters
            next_token(s).unwrap();

            if s.s_type != Flags::TOK_OPEN {
                s.s_type = Flags::TOK_ERROR;
            } else {
                let mut idx = 0;
                for _i in 0..arity {
                    next_token(s).unwrap();
                    ret.parameters.push(expr(s).unwrap());
                    if s.s_type != Flags::TOK_SEP {
                        break;
                    }
                    idx += 1;
                }
                if s.s_type != Flags::TOK_CLOSE || (idx != arity - 1) {
                    s.s_type = Flags::TOK_ERROR;
                } else {
                    next_token(s).unwrap();
                }
            }
        }
        Flags::TOK_OPEN => {
            next_token(s).unwrap();
            ret = list(s).unwrap();
            if s.s_type != Flags::TOK_CLOSE {
                s.s_type = Flags::TOK_ERROR;
            } else {
                next_token(s).unwrap();
            }
        }
        _ => {
            // todo: better error? Use NaN?
            ret = new_expr(Flags::TE_VARIABLE, None);
            s.s_type = Flags::TOK_ERROR;
            ret.value = 0.0;
        }
    }

    Ok(ret)
}

fn power(s: &mut State) -> Result<Expr> {
    let mut sign = 1;

    while s.s_type == Flags::TOK_INFIX && (s.function == add || s.function == sub) {
        if s.function == sub {
            sign = -sign;
        }
        next_token(s).unwrap();
    }

    let mut ret: Expr;

    if sign == 1 {
        ret = base(s).unwrap();
    } else {
        ret = new_expr(
            Flags::TE_FUNCTION1 | Flags::TE_FLAG_PURE,
            Some(vec![base(s).unwrap().clone()]),
        );
        ret.function = neg;
    }

    Ok(ret)
}

// todo: ifdef TE_POW_FROM_RIGHT
fn factor(s: &mut State) -> Result<Expr> {
    let mut ret = power(s).unwrap();

    // todo: check functions here
    while s.s_type == Flags::TOK_INFIX && s.function == pow {
        let f = s.function;
        next_token(s).unwrap();
        ret = new_expr(
            Flags::TE_FUNCTION2 | Flags::TE_FLAG_PURE,
            Some(vec![ret.clone(), power(s).unwrap().clone()]),
        );
        ret.function = f;
    }

    Ok(ret)
}

fn term(s: &mut State) -> Result<Expr> {
    let mut ret = factor(s).unwrap();

    while s.s_type == Flags::TOK_INFIX
        && (s.function == mul || s.function == div || s.function == fmod)
    {
        let f = s.function;
        next_token(s).unwrap();
        ret = new_expr(
            Flags::TE_FUNCTION2 | Flags::TE_FLAG_PURE,
            Some(vec![ret.clone(), factor(s).unwrap().clone()]),
        );
        ret.function = f;
    }

    Ok(ret)
}

fn expr(s: &mut State) -> Result<Expr> {
    let mut ret = term(s).unwrap();

    while s.s_type == Flags::TOK_INFIX && (s.function == add || s.function == sub) {
        let f = s.function;
        next_token(s).unwrap();
        ret = new_expr(
            Flags::TE_FUNCTION2 | Flags::TE_FLAG_PURE,
            Some(vec![ret.clone(), term(s).unwrap().clone()]),
        );
        ret.function = f;
    }

    Ok(ret)
}

fn list(s: &mut State) -> Result<Expr> {
    let mut ret = expr(s).unwrap();

    while s.s_type == Flags::TOK_SEP {
        next_token(s).unwrap();
        ret = new_expr(
            Flags::TE_FUNCTION2 | Flags::TE_FLAG_PURE,
            Some(vec![ret.clone(), expr(s).unwrap()]),
        );
        ret.function = comma;
    }

    Ok(ret)
}

fn optimize(n: &mut Expr) {
    // evaluates as much as possible
    if n.e_type == Flags::TE_CONSTANT {
        return;
    }
    if n.e_type == Flags::TE_VARIABLE {
        return;
    }

    if (n.e_type & Flags::TE_FLAG_PURE).bits() != 0 {
        let known = 1;
        let arity = arity!(n.e_type);

        for i in 0..arity {
            optimize(n.parameters.get_mut(i as usize).unwrap());
        }

        if known != 0 {
            n.value = eval(&n);
            n.e_type = Flags::TE_CONSTANT;
        }
    }
}

fn compile(expression: &str, variables: Option<Vec<Variable>>) -> Result<Option<Expr>> {
    let mut s = State::new(expression);
    if let Some(vars) = variables {
        s.lookup = vars;
    }

    arity!(s.s_type);
    next_token(&mut s).unwrap();
    let mut root = list(&mut s).unwrap();

    if s.s_type != Flags::TOK_END {
        return Ok(None);
    }

    optimize(&mut root);
    Ok(Some(root))
}

/// Interprets a string expression as a mathematical expresion, evaluates it and returns its result.
///
/// # Examples
///
/// ```
/// extern crate tinyexpr;
///
/// // "result" should contain a "4"
/// let result = tinyexpr::interp("2+2").unwrap();
/// ```
pub fn interp(expression: &str) -> Result<f64> {
    match compile(expression, None) {
        Ok(Some(expr)) => Ok(eval(&expr)),
        Err(e) => Err(e),
        _ => Err(error::TinyExprError::Other(String::from("NaN"))),
    }
}

// todo
fn eval(n: &Expr) -> f64 {
    match type_mask!(n.e_type) {
        Flags::TE_CONSTANT => n.value,
        Flags::TE_VARIABLE => n.bound as f64,
        Flags::TE_FUNCTION0
        | Flags::TE_FUNCTION1
        | Flags::TE_FUNCTION2
        | Flags::TE_FUNCTION3
        | Flags::TE_FUNCTION4
        | Flags::TE_FUNCTION5
        | Flags::TE_FUNCTION6
        | Flags::TE_FUNCTION7 => {
            match arity!(n.e_type) {
                // todo: REALLY need more function pointer types to avoid hacks like this 0.0 here...
                0 => ((*n).function)(0.0, 0.0),
                1 => ((*n).function)(eval(&n.parameters[0]), 0.0),
                2 => ((*n).function)(eval(&n.parameters[0]), eval(&n.parameters[1])),
                _ => panic!("todo: add more f. pointers (type is {})", arity!(n.e_type)),
            }
        }
        _ => 0.0,
    }
}
