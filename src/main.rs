use egg;
use egg::rewrite as rw;
use egg::Id;

type EGraph = egg::EGraph<LLVM, ()>;

egg::define_language! {
  pub enum LLVM {
    Size(u32),

    "const" = Constant([Id; 2]),
    "live-in" = LiveIn([Id; 2]),

    "add" = Add([Id; 3]),
    "mul" = Mul([Id; 3]),
    "trunc" = Trunc([Id; 3]),
    "sext" = SExt([Id; 3]),
    "select" = Select([Id; 4]),

    Symbol(egg::Symbol),
  }
}

fn build_rewrite(name: &str, lhs: &str, rhs: &str) -> egg::Rewrite<LLVM, ()> {
    let a: egg::Pattern<LLVM> = lhs.parse().unwrap();
    let b: egg::Pattern<LLVM> = rhs.parse().unwrap();
    rw!(name; a => b)
}

fn build_rewrite2(name: &str, lhs: &str, rhs: &str) -> Vec<egg::Rewrite<LLVM, ()>> {
    let name2 = format!("{}-2", name);
    vec![
        build_rewrite(name, lhs, rhs),
        build_rewrite(&name2, rhs, lhs),
    ]
}

fn trunc_binary(op: &str) -> Vec<egg::Rewrite<LLVM, ()>> {
    let name = format!("trunc-{}-1", op);
    let lhs = format!("({} ?new (trunc ?old ?new ?x) (trunc ?old ?new ?y))", op);
    let rhs = format!("(trunc ?old ?new ({} ?old ?x ?y))", op);
    build_rewrite2(&name, &lhs, &rhs)
}

fn rules() -> Vec<egg::Rewrite<LLVM, ()>> {
    let mut r = Vec::new();
    r.extend(
        vec![
            trunc_binary("add"),
            trunc_binary("mul"),
            rw!(
               "trunc-select";
               "(trunc ?old ?new (select ?old ?cond ?t ?f))"
               <=>
               "(select ?new ?cond (trunc ?old ?new ?t)
                                   (trunc ?old ?new ?f))"),
        ]
        .concat(),
    );
    r
}

fn saturate(expr: &egg::RecExpr<LLVM>) -> EGraph {
    egg::Runner::default().with_expr(&expr).run(&rules()).egraph
}

fn is_equivalent(x_s: &str, y_s: &str) -> bool {
    let x = x_s.parse().unwrap();
    let y = y_s.parse().unwrap();
    !saturate(&x).equivs(&x, &y).is_empty()
}

#[test]
fn trunc_add() {
    assert!(is_equivalent(
        "(add 8 (trunc 16 8 a) (trunc 16 8 b))",
        "(trunc 16 8 (add 16 a b))",
    ));
}

#[test]
fn trunc_mul() {
    assert!(is_equivalent(
        "(mul 8 (trunc 16 8 a) (trunc 16 8 b))",
        "(trunc 16 8 (mul 16 a b))"
    ));
}

#[test]
fn trunc_select() {
    assert!(is_equivalent(
        "(select 8 c (trunc 16 8 a) (trunc 16 8 b))",
        "(trunc 16 8 (select 16 c a b))"
    ))
}

fn main() {
    println!("Hello, world!");
}
