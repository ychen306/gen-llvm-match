use egg;
use egg::Id as Id;
use egg::rewrite as rw;

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
    Symbol(egg::Symbol),
  }
}

fn rewrite_trunc(op : &str) -> egg::Rewrite<LLVM, ()> {
  let name = format!("trunc-{}", op);
  let lhs : egg::Pattern<LLVM> =
    format!("({} ?new (trunc ?old ?new ?x) (trunc ?old ?new ?y))", op).parse().unwrap();
  let rhs : egg::Pattern<LLVM> =
    format!("(trunc ?old ?new ({} ?old ?x ?y))", op).parse().unwrap();
  rw!(name; lhs => rhs)
}

fn saturate(expr : &egg::RecExpr<LLVM>) -> EGraph {
  let mut rules = Vec::new();
  rules.push(rewrite_trunc("add"));
  
  egg::Runner::default().with_expr(&expr).run(&rules).egraph
}

fn is_equivalent(x_s : &str, y_s : &str) -> bool {
  let x = x_s.parse().unwrap();
  let y = y_s.parse().unwrap();
  !saturate(&x).equivs(&x, &y).is_empty()
}

#[test]
fn trunc_add() {
  assert!(is_equivalent(
      "(add 8 (trunc 16 8 a) (trunc 16 8 b))",
      "(trunc 16 8 (add 16 a b))"));
}

fn main() {
  println!("Hello, world!");
}
