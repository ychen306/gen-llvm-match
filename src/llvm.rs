use egg;
use egg::rewrite as rw;
pub use egg::Id;

pub type EGraph = egg::EGraph<LLVM, ()>;

egg::define_language! {
  // TODO: add floating point
  pub enum LLVM {
    Size(u32),

    "const" = Constant([Id; 2]),
    "live-in" = LiveIn([Id; 2]),

    "add" = Add([Id; 3]),
    "mul" = Mul([Id; 3]),
    "sub" = Sub([Id; 3]),

    "trunc" = Trunc([Id; 3]),
    "sext" = SExt([Id; 3]),
    "zext" = ZExt([Id; 3]),

    "slt" = SLT([Id; 3]),
    "sle" = SLE([Id; 3]),
    "sgt" = SGT([Id; 3]),
    "sge" = SGE([Id; 3]),

    "ult" = ULT([Id; 3]),
    "ule" = ULE([Id; 3]),
    "ugt" = UGT([Id; 3]),
    "uge" = UGE([Id; 3]),

    "eq" = EQ([Id; 3]),

    "not" = Not(Id),

    "select" = Select([Id; 4]),

    Symbol(egg::Symbol),
  }
}

fn build_rewrite(name: &str, lhs: &str, rhs: &str) -> egg::Rewrite<LLVM, ()> {
    let a: egg::Pattern<LLVM> = lhs.parse().unwrap();
    let b: egg::Pattern<LLVM> = rhs.parse().unwrap();
    rw!(name; { a } => { b })
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

fn power_of_two_ceil(n: u32) -> u32 {
    (n as f64).log2().ceil().powi(2) as u32
}

// (?op 32 (?ext 8 32 x) (?ext 8 32 y))
//  => (?ext 16 32 (?ext 8 16 x) (?ext 8 16 x))
fn add_precise(op: &str, ext: &str, old_bw: u32, new_bw: u32) -> Vec<egg::Rewrite<LLVM, ()>> {
    let small = power_of_two_ceil(old_bw + 1);
    if small < new_bw {
        let name = format!("{}-{}-precise-{}-{}", op, ext, old_bw, new_bw);
        let lhs = format!(
            "({op} {new} ({ext} {old} {new} ?x) ({ext} {old} {new} ?y))",
            op = op,
            old = old_bw,
            new = new_bw,
            ext = ext
        );
        let rhs = format!(
            "({ext} {small} {new}
                           ({op} {small} ({ext} {old} {small} ?x) ({ext} {old} {small} ?y)))",
            op = op,
            old = old_bw,
            small = small,
            new = new_bw,
            ext = ext
        );
        build_rewrite2(&name, &lhs, &rhs)
    } else {
        Vec::new()
    }
}

// (sub 32 (zext 8 32 x) (zext 8 32 y))
//   => (*sext* 16 32 (sub (zext 8 16 x) (zext 8 16 y)))
fn sub_precise(old_bw: u32, new_bw: u32) -> Vec<egg::Rewrite<LLVM, ()>> {
    let small = power_of_two_ceil(old_bw + 1);
    if small == new_bw && false {
        Vec::new()
    } else {
        let name = format!("unsigned-sub-precise-{}-{}", old_bw, new_bw);
        let lhs = format!(
            "(sub {new} (zext {old} {new} ?x) (zext {old} {new} ?y))",
            old = old_bw,
            new = new_bw,
        );
        let rhs = format!(
            "(sext {small} {new}
                           (sub {small} (zext {old} {small} ?x) (zext {old} {small} ?y)))",
            old = old_bw,
            small = small,
            new = new_bw,
        );
        build_rewrite2(&name, &lhs, &rhs)
    }
}

fn cmp_sext(old_bw: u32, new_bw1: u32, new_bw2: u32) -> Vec<egg::Rewrite<LLVM, ()>> {
    if old_bw > new_bw1 || old_bw > new_bw2 || new_bw1 >= new_bw2 {
        return Vec::new();
    }

    let cmps = ["slt", "sle", "sgt", "sge", "eq"];
    let mut rules = Vec::new();

    for cmp in cmps.iter() {
        let name = format!("{}-sext-{}-{}-{}", cmp, old_bw, new_bw1, new_bw2);
        let lhs = if new_bw1 == old_bw {
            format!("({cmp} {old} ?x ?y)", old = old_bw, cmp = cmp)
        } else {
            format!(
                "({cmp} {new} (sext {old} {new} ?x) (sext {old} {new} ?y))",
                cmp = cmp,
                old = old_bw,
                new = new_bw1
            )
        };
        let rhs = format!(
            "({cmp} {new} (sext {old} {new} ?x) (sext {old} {new} ?y))",
            cmp = cmp,
            old = old_bw,
            new = new_bw2
        );
        rules.extend(build_rewrite2(&name, &lhs, &rhs));
    }

    rules
}

pub fn rules() -> Vec<egg::Rewrite<LLVM, ()>> {
    let mut r = vec![
        rw!("add-assoc"; "(add ?bw ?a ?b)" => "(add ?bw ?b ?a)"),
        rw!("mul-assoc"; "(mul ?bw ?a ?b)" => "(mul ?bw ?b ?a)"),
        rw!("add-comm"; 
        "(add ?bw (add ?bw ?a ?b) ?c)"
        =>
        "(add ?bw ?a (add ?bw ?b ?c))"),
        rw!("mul-comm"; 
            "(mul ?bw (mul ?bw ?a ?b) ?c)"
            =>
            "(mul ?bw ?a (mul ?bw ?b ?c))"),
    ];
    r.extend(
        vec![
            trunc_binary("add"),
            trunc_binary("sub"),
            trunc_binary("mul"),
            rw!(
      "trunc-select";
      "(trunc ?old ?new (select ?old ?cond ?t ?f))"
      <=>
      "(select ?new ?cond (trunc ?old ?new ?t)
                                   (trunc ?old ?new ?f))"),
            rw!("slt-sgt"; "(slt ?bw ?a ?b)" <=> "(sgt ?bw ?b ?a)"),
            rw!("sle-sge"; "(sle ?bw ?a ?b)" <=> "(sge ?bw ?b ?a)"),
            rw!("ult-ugt"; "(ult ?bw ?a ?b)" <=> "(ugt ?bw ?b ?a)"),
            rw!("ule-uge"; "(ule ?bw ?a ?b)" <=> "(uge ?bw ?b ?a)"),
        ]
        .concat(),
    );

    let bitwidths = [8, 16, 32, 64];
    for i in bitwidths.iter() {
        for j in bitwidths.iter() {
            if j > i {
                let name = format!("sext-zero-{i}-{j}", i = i, j = j);
                let lhs = format!("(sext {i} {j} (const {i} 0))", i = i, j = j);
                let rhs = format!("(const {j} 0)", j = j);
                r.extend(build_rewrite2(&name, &lhs, &rhs));
                r.extend(add_precise("sub", "sext", *i, *j));
                r.extend(add_precise("add", "sext", *i, *j));
                r.extend(add_precise("add", "zext", *i, *j));
                r.extend(sub_precise(*i, *j));
            }
            for k in bitwidths.iter() {
                r.extend(cmp_sext(*i, *j, *k));
                // ((? j k (? i j x)))
                if k < j && j > i && k != i {
                    let lhs = format!("(trunc {j} {k} (sext {i} {j} ?x))", i = i, j = j, k = k);
                    let lhs_z = format!("(trunc {j} {k} (zext {i} {j} ?x))", i = i, j = j, k = k);

                    let rhs = if k > i {
                        format!("(sext {i} {k} ?x)", i = i, k = k)
                    } else {
                        format!("(trunc {i} {k} ?x)", i = i, k = k)
                    };
                    let rhs_z = if k > i {
                        format!("(zext {i} {k} ?x)", i = i, k = k)
                    } else {
                        format!("(trunc {i} {k} ?x)", i = i, k = k)
                    };

                    let name = format!("trunc-sext-{i}-{j}-{k}", i = i, j = j, k = k);
                    let name_z = format!("trunc-zext-{i}-{j}-{k}", i = i, j = j, k = k);
                    r.extend(build_rewrite2(&name, &lhs, &rhs));
                    r.extend(build_rewrite2(&name_z, &lhs_z, &rhs_z));
                } else if k > j && j > i {
                    let name = format!("sext-sext-{i}-{j}-{k}", i = i, j = j, k = k);
                    let lhs = format!("(sext {j} {k} (sext {i} {j} ?x))", i = i, j = j, k = k);
                    let rhs = format!("(sext {i} {k} ?x)", i = i, k = k);
                    r.extend(build_rewrite2(&name, &lhs, &rhs));

                    let name_z = format!("zext-zext-{i}-{j}-{k}", i = i, j = j, k = k);
                    let lhs_z = format!("(zext {j} {k} (zext {i} {j} ?x))", i = i, j = j, k = k);
                    let rhs_z = format!("(zext {i} {k} ?x)", i = i, k = k);
                    r.extend(build_rewrite2(&name_z, &lhs_z, &rhs_z));
                }
            }
        }
    }

    r
}

pub fn saturate(expr: &egg::RecExpr<LLVM>) -> (EGraph, Id) {
    let runner = egg::Runner::default().with_expr(&expr).run(&rules());
    (runner.egraph, runner.roots[0])
}

pub fn is_equivalent(x_s: &str, y_s: &str) -> bool {
    let x = x_s.parse().unwrap();
    let y = y_s.parse().unwrap();
    let (egraph, _) = saturate(&x);
    !egraph.equivs(&x, &y).is_empty()
}
