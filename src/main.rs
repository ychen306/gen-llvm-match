mod llvm;

use egg::Language;
use llvm::EGraph;
use std::cmp;
use llvm::is_equivalent;
use std::collections::HashMap;
use std::path::Path;

fn main() {
    let sad16 = format!("(add 16 {x} {x})", x=abs16());
    let (egraph, _) = llvm::saturate(&sad16.parse().unwrap());
    //egraph.dot().to_png(Path::new("sad16.png")).unwrap();
    println!("num enodes {}", egraph.total_size());
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
    ));
}

#[test]
fn trunc_sext() {
    assert!(is_equivalent(
        "(trunc 32 16 (sext 8 32 x))",
        "(sext 8 16 x)"
    ));
}

#[test]
fn lt_and_gt() {
    assert!(is_equivalent("(slt 8 a b)", "(sgt 8 b a)"));
}

#[test]
fn trunc_sext_add() {
    assert!(is_equivalent(
        "(trunc 32 16 (add 32 (sext 8 32 x) (sext 8 32 y)))",
        "(add 16 (sext 8 16 x) (sext 8 16 y))"
    ));
}

#[test]
fn test_sub_precise() {
    assert!(is_equivalent(
        "(sub 32 (sext 8 32 x) (sext 8 32 y))",
        "(sext 16 32 (sub 16 (sext 8 16 x) (sext 8 16 y)))"
    ));
}

#[test]
fn test_cmp_sext() {
    assert!(is_equivalent(
        "(slt 16 (sub 16 (sext 8 16 x) (sext 8 16 y)) (const 16 0))",
        "(slt 32 (sub 32 (sext 8 32 x) (sext 8 32 y)) (const 32 0))"
    ));
}

fn abs16() -> String {
    let diff16 = "(sub 16 (zext 8 16 x) (zext 8 16 y))";
    format!(
        "(select 16 (slt 16 {diff16} (const 16 0))
                    {diff16}
                    (sub 16 (zext 8 16 y) (zext 8 16 x)))",
        diff16 = diff16
    )
}

fn abs32() -> String {
    let diff32 = "(sub 32 (zext 8 32 x) (zext 8 32 y))";
    format!(
        "(select 32 (slt 32 {diff32} (const 32 0))
                    {diff32}
                    (sub 32 (zext 8 32 y) (zext 8 32 x)))",
        diff32 = diff32
    )
}

#[test]
fn trunc_abs() {
    let abs16_2 = format!("(trunc 32 16 {})", abs32());
    assert!(is_equivalent(&abs16(), &abs16_2));
}

#[test]
fn add_abs() {
    let sad16 = format!("(add 16 {x} {x})", x = abs16());
    let sad32 = format!("(trunc 32 16 (add 32 {x} {x}))", x = abs32());
    assert!(is_equivalent(&sad16, &sad32));
}

#[test]
fn reorder_add() {
    assert!(is_equivalent(
        "(add 8 a (add 8 b (add 8 c d)))",
        "(add 8 d (add 8 c (add 8 b a)))"
    ));
}

#[test]
fn reorder_mul() {
    assert!(is_equivalent(
        "(mul 8 a (mul 8 b (mul 8 c d)))",
        "(mul 8 d (mul 8 c (mul 8 b a)))"
    ));
}
