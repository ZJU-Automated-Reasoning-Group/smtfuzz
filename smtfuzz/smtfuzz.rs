use anyhow::Result;
use clap::Parser;
use env_logger::Env;
use rand::rngs::StdRng;
use rand::seq::SliceRandom;
use rand::{Rng, SeedableRng};

/// A lightweight Rust port of smtfuzz.py that emits random SMT-LIB problems.
///
/// This is intentionally minimal compared to the Python original: it supports
/// a subset of strategies and logics sufficient for basic fuzzing.
#[derive(Parser, Debug)]
#[command(name = "smtfuzz")] 
#[command(about = "Generate random SMT-LIB benchmarks", version)]
struct Args {
    /// Strategy for generation: noinc (non-incremental), bool, cnf, strictcnf, or random
    #[arg(long = "strategy", default_value = "noinc")]
    strategy: String,

    /// Logic to generate (e.g., QF_BV, BOOL, QBF). Use 'random' to choose randomly
    #[arg(long = "logic", default_value = "random")]
    logic: String,

    /// Random seed
    #[arg(long = "seed")]
    seed: Option<u64>,

    /// Ratio of variables to clauses in CNF generation
    #[arg(long = "cnfratio", default_value_t = 5)]
    ratio: usize,

    /// Max number of assertions
    #[arg(long = "cntsize", default_value_t = 66)]
    cntsize: usize,

    /// Test SMT optimization (enables printing of (get-objectives) after checks)
    #[arg(long = "smtopt", default_value_t = 0)]
    smtopt: i32,

    /// Test Max-SMT (will emit assert-soft alongside hard assertions)
    #[arg(long = "maxsmt", default_value_t = 0)]
    maxsmt: i32,

    /// Test QBF solving (enables quantifiers in BOOL/QBF)
    #[arg(long = "qbf", default_value_t = 0)]
    qbf: i32,

    /// Test Max-SAT (assert-soft only, propositional layer)
    #[arg(long = "maxsat", default_value_t = 0)]
    maxsat: i32,

    /// Test quantifier elimination (flag only; generation remains random)
    #[arg(long = "qe", default_value_t = 0)]
    qe: i32,

    /// Request unsat core (will emit (get-unsat-core))
    #[arg(long = "unsat_core", default_value_t = 0)]
    unsat_core: i32,

    /// Request proof (will emit (get-proof))
    #[arg(long = "proof", default_value_t = 0)]
    proof: i32,
}

const STRATEGIES: &[&str] = &["noinc", "bool", "cnf", "strictcnf", "ncnf", "CNFexp"];
const LOGICS: &[&str] = &[
    // Propositional / QBF
    "BOOL", "QBF",
    // Bit-vectors and combos
    "QF_BV", "BV", "QF_AUFBV", "AUFBV", "QF_ABV",
    // Arrays, UF, and combos
    "QF_AX", "QF_UF", "UF", "QF_UFLIA", "QF_UFLRA", "UFLIA", "UFLRA", "QF_AUFLIA",
    // Arithmetic
    "QF_LIA", "LIA", "QF_LRA", "LRA", "QF_NIA", "NIA", "QF_NRA", "NRA", "IDL", "RDL",
    // Reals/FP
    "QF_FP", "FP", "QF_FPLRA", "FPLRA",
    // Strings and sequences
    "QF_S", "QF_SLIA", "QF_SNIA", "QF_SLIRA", "SEQ", "STRSET",
    // Sets/Bags
    "SET", "BAG",
    // Misc
    "QF_UFC", "UFC", "BVINT",
];

struct Ctx<'a> {
    rng: &'a mut StdRng,
    logic: String,
    // feature toggles inferred from logic/args
    test_qbf: bool,
    test_smt_opt: bool,
    test_max_smt: bool,
    test_max_sat: bool,
    test_unsat_core: bool,
    test_proof: bool,
    test_string: bool,
    test_string_lia: bool,
    test_seq: bool,
    test_set_bapa: bool,
    test_bag_bapa: bool,
    test_bvint: bool,
    test_arrays: bool,
    test_seplog: bool,
    test_fp: bool,
    test_fp_lra: bool,
    test_ufc: bool,
    // presence of base sorts (for arrays etc.)
    has_bv: bool,
    has_int: bool,
    has_real: bool,
    has_string: bool,
    // assertion bookkeeping
    assert_id: usize,
    all_assertions: Vec<String>,
    // quantifier control
    emitted_quant: bool,
    prefer_quant_in_non_qf: bool,
}

fn main() -> Result<()> {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();
    let args = Args::parse();

    let mut rng: StdRng = match args.seed {
        Some(s) => StdRng::seed_from_u64(s),
        None => StdRng::from_entropy(),
    };

    let logic = choose_logic(&args, &mut rng);
    let strategy = choose_strategy(&args, &mut rng);

    emit_set_logic(&logic);
    emit_set_options(&args);

    let mut ctx = build_ctx(&args, &logic, &mut rng);

    match strategy.as_str() {
        "bool" => gen_bool(&mut ctx, args.cntsize),
        "cnf" => gen_cnf(&mut ctx, args.ratio, args.cntsize, false),
        "strictcnf" => gen_cnf(&mut ctx, args.ratio, args.cntsize, true),
        "ncnf" => gen_ncnf(&mut ctx, args.ratio, args.cntsize),
        "CNFexp" => gen_cnfexp(&mut ctx, args.ratio, args.cntsize),
        _ => gen_noinc(&mut ctx, args.ratio, args.cntsize),
    }

    println!("(check-sat)");
    if ctx.test_smt_opt { println!("(get-objectives)"); }
    if ctx.test_unsat_core { println!("(get-unsat-core)"); }
    if ctx.test_proof { println!("(get-proof)"); }
    Ok(())
}

fn choose_strategy(args: &Args, rng: &mut StdRng) -> String {
    if args.strategy == "random" {
        STRATEGIES.choose(rng).unwrap().to_string()
    } else {
        args.strategy.clone()
    }
}

fn choose_logic(args: &Args, rng: &mut StdRng) -> String {
    if args.logic == "random" {
        LOGICS.choose(rng).unwrap().to_string()
    } else if LOGICS.contains(&args.logic.as_str()) {
        args.logic.clone()
    } else {
        // Fallback to a close match: QF_BV for bit-vectors, BOOL otherwise
        if args.logic.contains("BV") { "QF_BV".to_string() } else { "BOOL".to_string() }
    }
}

fn emit_set_logic(logic: &str) {
    println!("(set-logic {})", logic);
}

fn emit_set_options(args: &Args) {
    // A few generic options, mirroring spirit of smtfuzz.py set_options
    println!("(set-option :produce-models true)");
    if args.unsat_core != 0 { println!("(set-option :produce-unsat-cores true)"); }
    if args.proof != 0 { println!("(set-option :produce-proofs true)"); }
    if args.smtopt != 0 {
        // provide trivial objectives so (get-objectives) is meaningful
        println!("(maximize 0)");
        println!("(minimize 0)");
    }
}

fn build_ctx<'a>(args: &Args, logic: &str, rng: &'a mut StdRng) -> Ctx<'a> {
    let mut ctx = Ctx {
        rng,
        logic: logic.to_string(),
        test_qbf: false,
        test_smt_opt: args.smtopt != 0,
        test_max_smt: args.maxsmt != 0,
        test_max_sat: args.maxsat != 0,
        test_unsat_core: args.unsat_core != 0,
        test_proof: args.proof != 0,
        test_string: false,
        test_string_lia: false,
        test_seq: false,
        test_set_bapa: false,
        test_bag_bapa: false,
        test_bvint: false,
        test_arrays: false,
        test_seplog: false,
        test_fp: false,
        test_fp_lra: false,
        test_ufc: false,
        has_bv: false,
        has_int: false,
        has_real: false,
        has_string: false,
        assert_id: 0,
        all_assertions: Vec::new(),
        emitted_quant: false,
        prefer_quant_in_non_qf: false,
    };

    if ctx.logic == "QBF" { ctx.test_qbf = true; }
    match ctx.logic.as_str() {
        "QF_S" => ctx.test_string = true,
        "QF_SLIA" | "QF_SNIA" | "QF_SLIRA" | "SEQ" => { ctx.test_string_lia = true; if ctx.logic == "SEQ" { ctx.test_seq = true; } },
        "QF_FP" | "FP" => ctx.test_fp = true,
        "QF_FPLRA" | "FPLRA" => ctx.test_fp_lra = true,
        "QF_UFC" | "UFC" => ctx.test_ufc = true,
        "SET" | "STRSET" => { ctx.test_set_bapa = true; if ctx.logic == "STRSET" { ctx.test_string_lia = true; } },
        "BAG" => ctx.test_bag_bapa = true,
        "SEPLOG" => ctx.test_seplog = true,
        "BVINT" => ctx.test_bvint = true,
        _ => {}
    }

    // Heuristics for base sort presence and arrays
    if ctx.logic.contains("BV") { ctx.has_bv = true; }
    if ctx.logic.contains("INT") || ctx.logic.contains("LIA") || ctx.logic.contains("IDL") || ctx.logic.contains("NIA") { ctx.has_int = true; }
    if ctx.logic.contains("REAL") || ctx.logic.contains("LRA") || ctx.logic.contains("RDL") || ctx.logic.contains("NRA") { ctx.has_real = true; }
    if ctx.test_string || ctx.test_string_lia || ctx.test_seq || ctx.logic.contains("STR") { ctx.has_string = true; }
    if ctx.logic.contains("ARR") || ctx.logic.contains("AX") || ctx.logic.contains("Array") || ctx.logic.contains("UFC") {
        ctx.test_arrays = true;
    }
    // prefer adding quantifiers when logic is not quantifier-free
    if !ctx.logic.starts_with("QF_") { ctx.prefer_quant_in_non_qf = true; }
    ctx
}

fn gen_bool(ctx: &mut Ctx, cntsize: usize) {
    let num_vars = (cntsize.max(3) / 2).clamp(3, 64);
    for i in 0..num_vars { println!("(declare-const b{} Bool)", i); }

    let mut asserts_left = cntsize;
    while asserts_left > 0 {
        let expr = random_bool_expr(num_vars, 0, ctx.rng);
        emit_assert(ctx, &expr);
        asserts_left -= 1;
        maybe_midstream_check(ctx);
    }
}

fn random_bool_expr(num_vars: usize, depth: usize, rng: &mut StdRng) -> String {
    if depth > 3 || rng.gen_bool(0.3) {
        let v = rng.gen_range(0..num_vars);
        let lit = if rng.gen_bool(0.5) { format!("b{}", v) } else { format!("(not b{})", v) };
        return lit;
    }
    let k = rng.gen_range(2..=3);
    let mut parts: Vec<String> = Vec::new();
    for _ in 0..k { parts.push(random_bool_expr(num_vars, depth + 1, rng)); }
    let op = ["and", "or", "xor"].choose(rng).unwrap();
    format!("({} {} )", op, parts.join(" "))
}

fn gen_cnf(ctx: &mut Ctx, ratio: usize, cntsize: usize, strict: bool) {
    // CNF over Bool only; if logic is non-BOOL, still permitted as propositional layer
    let num_clauses = cntsize.clamp(1, 2000);
    let num_vars = (num_clauses / ratio.max(1)).clamp(1, 200);
    for i in 0..num_vars { println!("(declare-const p{} Bool)", i); }

    for _ in 0..num_clauses {
        let k = if strict { 3 } else { ctx.rng.gen_range(2..=5) };
        let mut lits: Vec<String> = Vec::new();
        for _ in 0..k {
            let v = ctx.rng.gen_range(0..num_vars);
            let base = format!("p{}", v);
            let lit = if ctx.rng.gen_bool(0.5) { base } else { format!("(not {})", base) };
            lits.push(lit);
        }
        emit_assert(ctx, &format!("(or {})", lits.join(" ")));
        maybe_midstream_check(ctx);
    }

    // In non-BOOL logics, add a few irrelevant declarations to exercise parsers
    if ctx.logic.contains("BV") {
        for i in 0..ctx.rng.gen_range(0..=3) { println!("(declare-const x{}_bv (_ BitVec 32))", i); }
    }
}

fn gen_noinc(ctx: &mut Ctx, _ratio: usize, cntsize: usize) {
    if ctx.logic.contains("BV") {
        gen_noinc_bv(ctx, cntsize);
        if ctx.test_arrays { gen_arrays(ctx, 32, 32, cntsize / 4); }
    } else if ctx.logic.contains("IDL") || ctx.logic.contains("RDL") || ctx.logic.contains("LIA") || ctx.logic.contains("LRA") || ctx.logic.contains("NIA") || ctx.logic.contains("NRA") || ctx.logic.contains("QF_LIA") || ctx.logic.contains("QF_LRA") || ctx.logic.contains("QF_NIA") || ctx.logic.contains("QF_NRA") {
        gen_noinc_arith(ctx, cntsize);
        if ctx.test_arrays { gen_arrays(ctx, 0, 0, cntsize / 4); }
    } else if ctx.test_string || ctx.test_string_lia || ctx.test_seq {
        gen_noinc_strings(ctx, cntsize);
        if ctx.test_arrays && ctx.has_int { gen_arrays(ctx, 0, 3, cntsize / 4); } // Int->String arrays
    } else if ctx.test_fp || ctx.test_fp_lra {
        gen_noinc_fp(ctx, cntsize);
    } else if ctx.test_ufc {
        gen_noinc_uf(ctx, cntsize);
    } else if ctx.test_set_bapa || ctx.test_bag_bapa {
        gen_noinc_sets_bags(ctx, cntsize);
    } else if ctx.test_bvint {
        gen_noinc_bvint(ctx, cntsize);
    } else if ctx.test_seplog {
        gen_noinc_seplog(ctx, cntsize);
    } else {
        // Fallback to Bool no-inc
        gen_bool(ctx, cntsize);
    }
}

fn gen_noinc_bv(ctx: &mut Ctx, cntsize: usize) {
    let num_vars = (cntsize / 3).clamp(2, 64);
    for i in 0..num_vars { println!("(declare-const x{} (_ BitVec 32))", i); }
    // maybe some arrays over BV
    if ctx.rng.gen_bool(0.4) {
        for a in 0..ctx.rng.gen_range(1..=2) { println!("(declare-const A{} (Array (_ BitVec 32) (_ BitVec 32)))", a); }
    }

    let mut left = cntsize;
    while left > 0 {
        let e1 = random_bv_expr(num_vars, 0, ctx.rng);
        let e2 = random_bv_expr(num_vars, 0, ctx.rng);
        let cmp = ["=", "=", "=", "bvult", "bvule", "bvugt", "bvuge"].choose(ctx.rng).unwrap();
        emit_assert(ctx, &format!("({} {} {})", cmp, e1, e2));
        left -= 1;
        if ctx.rng.gen_bool(0.2) && ctx.rng.gen_bool(0.5) {
            // exercise arrays
            let i = ctx.rng.gen_range(0..num_vars);
            let v = ctx.rng.gen_range(0..num_vars);
            println!("(assert (= (select A0 x{}) x{}))", i, v);
        }
        // Occasionally emit a quantified BV assertion when logic allows quantifiers
        if ctx.prefer_quant_in_non_qf && !ctx.emitted_quant && ctx.rng.gen_bool(0.4) {
            maybe_quantified_assert_bv(ctx);
            ctx.emitted_quant = true;
        } else if ctx.rng.gen_bool(0.15) {
            maybe_quantified_assert_bv(ctx);
        }
        maybe_midstream_check(ctx);
    }
}

fn random_bv_expr(num_vars: usize, depth: usize, rng: &mut StdRng) -> String {
    if depth > 3 || rng.gen_bool(0.25) {
        if rng.gen_bool(0.4) {
            // literal
            let v: u32 = rng.gen();
            format!("(_ bv{} 32)", v)
        } else {
            // variable
            let i = rng.gen_range(0..num_vars);
            format!("x{}", i)
        }
    } else {
        // binary op
        let op = [
            "bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", 
            "bvshl", "bvlshr", "bvudiv", "bvurem",
        ]
        .choose(rng)
        .unwrap();
        let a = random_bv_expr(num_vars, depth + 1, rng);
        let b = random_bv_expr(num_vars, depth + 1, rng);
        format!("({} {} {})", op, a, b)
    }
}

fn gen_noinc_sets_bags(ctx: &mut Ctx, cntsize: usize) {
    let num_sets = (cntsize / 6).clamp(1, 8);
    for i in 0..num_sets { println!("(declare-const S{} (Set Int))", i); }
    if ctx.test_bag_bapa {
        for i in 0..num_sets { println!("(declare-const B{} (Bag Int))", i); }
    }
    let mut left = cntsize;
    while left > 0 {
        // set ops: union, inter, subset, member
        let expr = if ctx.rng.gen_bool(0.6) {
            let a = ctx.rng.gen_range(0..num_sets);
            let b = ctx.rng.gen_range(0..num_sets);
            let op = ["union", "intersection", "subset", "="].choose(ctx.rng).unwrap();
            match *op {
                "union" => format!("(= (set.union S{} S{}) S{})", a, b, ctx.rng.gen_range(0..num_sets)),
                "intersection" => format!("(= (set.inter S{} S{}) S{})", a, b, ctx.rng.gen_range(0..num_sets)),
                "subset" => format!("(set.subset S{} S{})", a, b),
                _ => format!("(= S{} S{})", a, b),
            }
        } else {
            let a = ctx.rng.gen_range(0..num_sets);
            format!("(set.member {} S{})", ctx.rng.gen_range(-5..=5), a)
        };
        emit_assert(ctx, &expr);
        left -= 1;
        maybe_midstream_check(ctx);
    }
}

fn gen_noinc_bvint(ctx: &mut Ctx, cntsize: usize) {
    let num_bv = (cntsize / 4).clamp(1, 16);
    let num_int = (cntsize / 6).clamp(1, 12);
    for i in 0..num_bv { println!("(declare-const xb{} (_ BitVec 32))", i); }
    for i in 0..num_int { println!("(declare-const xi{} Int)", i); }
    let mut left = cntsize;
    while left > 0 {
        // mix casts and comparisons
        let e = match ctx.rng.gen_range(0..3) {
            0 => {
                let a = ctx.rng.gen_range(0..num_bv);
                let b = ctx.rng.gen_range(0..num_bv);
                format!("(= (bv2int xb{}) (bv2int xb{}))", a, b)
            }
            1 => {
                let a = ctx.rng.gen_range(0..num_int);
                format!("(= (int2bv 32 xi{}) (_ bv{} 32))", a, ctx.rng.gen_range(0..=255))
            }
            _ => {
                let a = ctx.rng.gen_range(0..num_bv);
                let b = ctx.rng.gen_range(0..num_int);
                format!("(= (bv2int xb{}) xi{})", a, b)
            }
        };
        emit_assert(ctx, &e);
        left -= 1;
        maybe_midstream_check(ctx);
    }
}

fn gen_noinc_arith(ctx: &mut Ctx, cntsize: usize) {
    let num_int = (cntsize / 4).clamp(1, 16);
    let num_real = (cntsize / 6).clamp(0, 12);
    for i in 0..num_int { println!("(declare-const i{} Int)", i); }
    for r in 0..num_real { println!("(declare-const r{} Real)", r); }

    let mut left = cntsize;
    while left > 0 {
        if num_real > 0 && ctx.rng.gen_bool(0.3) {
            let e1 = random_real_expr(num_real, 0, ctx.rng);
            let e2 = random_real_expr(num_real, 0, ctx.rng);
            let cmp = ["=", "<", "<=", ">", ">=", "="] .choose(ctx.rng).unwrap();
            emit_assert(ctx, &format!("({} {} {})", cmp, e1, e2));
        } else {
            let e1 = random_int_expr(num_int, 0, ctx.rng);
            let e2 = random_int_expr(num_int, 0, ctx.rng);
            let cmp = ["=", "<", "<=", ">", ">=", "="] .choose(ctx.rng).unwrap();
            emit_assert(ctx, &format!("({} {} {})", cmp, e1, e2));
        }
        left -= 1;
        if ctx.prefer_quant_in_non_qf && !ctx.emitted_quant && ctx.rng.gen_bool(0.4) {
            maybe_quantified_assert(ctx);
            ctx.emitted_quant = true;
        } else if ctx.rng.gen_bool(0.15) {
            maybe_quantified_assert(ctx);
        }
        maybe_midstream_check(ctx);
    }
}

fn random_int_expr(num_vars: usize, depth: usize, rng: &mut StdRng) -> String {
    if num_vars == 0 || depth > 3 || rng.gen_bool(0.3) {
        if rng.gen_bool(0.5) { format!("{}", rng.gen_range(-10..=10)) } else { format!("i{}", rng.gen_range(0..num_vars)) }
    } else {
        let op = ["+", "-", "*"].choose(rng).unwrap();
        let a = random_int_expr(num_vars, depth + 1, rng);
        let b = random_int_expr(num_vars, depth + 1, rng);
        format!("({} {} {})", op, a, b)
    }
}

fn random_real_expr(num_vars: usize, depth: usize, rng: &mut StdRng) -> String {
    if num_vars == 0 || depth > 3 || rng.gen_bool(0.3) {
        if rng.gen_bool(0.5) { format!("{}.0", rng.gen_range(-10..=10)) } else { format!("r{}", rng.gen_range(0..num_vars)) }
    } else {
        let op = ["+", "-", "*"].choose(rng).unwrap();
        let a = random_real_expr(num_vars, depth + 1, rng);
        let b = random_real_expr(num_vars, depth + 1, rng);
        format!("({} {} {})", op, a, b)
    }
}

fn gen_noinc_strings(ctx: &mut Ctx, cntsize: usize) {
    let num_vars = (cntsize / 3).clamp(2, 32);
    for i in 0..num_vars { println!("(declare-const s{} String)", i); }
    let mut left = cntsize;
    while left > 0 {
        // mix equality, contains, prefix/suffix, and length constraints
        let choice = ctx.rng.gen_range(0..4);
        let expr = match choice {
            0 => {
                let a = ctx.rng.gen_range(0..num_vars);
                let b = ctx.rng.gen_range(0..num_vars);
                format!("(= (str.++ s{} s{}) s{})", a, b, ctx.rng.gen_range(0..num_vars))
            }
            1 => {
                let a = ctx.rng.gen_range(0..num_vars);
                let b = ctx.rng.gen_range(0..num_vars);
                format!("(str.contains s{} s{})", a, b)
            }
            2 => {
                let a = ctx.rng.gen_range(0..num_vars);
                format!("(= (str.len s{}) {})", a, ctx.rng.gen_range(0..=20))
            }
            3 => {
                let a = ctx.rng.gen_range(0..num_vars);
                let b = ctx.rng.gen_range(0..num_vars);
                format!("(= s{} (str.++ s{} \"lit\"))", a, b)
            }
            _ => {
                let a = ctx.rng.gen_range(0..num_vars);
                let b = ctx.rng.gen_range(0..num_vars);
                if ctx.test_seq {
                    format!("(= (seq.len s{}) (seq.len s{}))", a, b)
                } else {
                    format!("(= (str.substr s{} 0 2) (str.substr s{} 1 2))", a, b)
                }
            }
        };
        emit_assert(ctx, &expr);
        left -= 1;
        maybe_midstream_check(ctx);
    }
}

fn gen_noinc_fp(ctx: &mut Ctx, cntsize: usize) {
    // Single-precision variables
    let num_vars = (cntsize / 3).clamp(2, 32);
    for i in 0..num_vars { println!("(declare-const f{} (_ FloatingPoint 8 24))", i); }
    let mut left = cntsize;
    while left > 0 {
        let a = ctx.rng.gen_range(0..num_vars);
        let b = ctx.rng.gen_range(0..num_vars);
        let c = ctx.rng.gen_range(0..num_vars);
        let exprs = [
            format!("(= (fp.add RNE f{} f{}) f{})", a, b, c),
            format!("(fp.lt f{} f{})", a, b),
            format!("(= (fp.mul RNE f{} f{}) f{})", a, b, c),
        ];
        let e = exprs.choose(ctx.rng).unwrap().clone();
        emit_assert(ctx, &e);
        left -= 1;
        maybe_midstream_check(ctx);
    }
}

fn gen_noinc_seplog(ctx: &mut Ctx, cntsize: usize) {
    // Very lightweight separation-logic flavored constraints using uninterpreted preds
    // (since full heap semantics are non-trivial). We simulate with UF predicates.
    println!("(declare-fun pt (Int Int) Bool)");
    println!("(declare-fun disj (Int Int Int Int) Bool)");
    for i in 0..6 { println!("(declare-const l{} Int)", i); }
    for i in 0..6 { println!("(declare-const r{} Int)", i); }
    let mut left = cntsize;
    while left > 0 {
        let a = ctx.rng.gen_range(0..6);
        let b = ctx.rng.gen_range(0..6);
        let c = ctx.rng.gen_range(0..6);
        let d = ctx.rng.gen_range(0..6);
        let exprs = [
            format!("(pt l{} r{})", a, b),
            format!("(disj l{} r{} l{} r{})", a, b, c, d),
            format!("(=> (pt l{} r{}) (not (pt l{} r{})))", a, b, c, d),
        ];
        let e = exprs.choose(ctx.rng).unwrap().clone();
        emit_assert(ctx, &e);
        left -= 1;
        maybe_midstream_check(ctx);
    }
}

fn emit_assert(ctx: &mut Ctx, body: &str) {
    // Decide soft/hard, and optionally name
    let use_soft = ctx.test_max_sat || ctx.test_max_smt && ctx.rng.gen_bool(0.5);
    let name_it = ctx.test_unsat_core || ctx.test_proof;
    if use_soft {
        println!("(assert-soft {} :weight {})", body, ctx.rng.gen_range(1..=20));
    } else if name_it {
        ctx.assert_id += 1;
        let name = format!("IP_{}", ctx.assert_id);
        println!("(assert (! {} :named {}))", body, name);
        ctx.all_assertions.push(name);
    } else {
        println!("(assert {})", body);
    }
}

fn maybe_midstream_check(ctx: &mut Ctx) {
    if ctx.rng.gen_bool(0.05) {
        if ctx.rng.gen_bool(0.3) { println!("(push 1)"); }
        println!("(check-sat)");
        if ctx.test_smt_opt { println!("(get-objectives)"); }
        if ctx.test_unsat_core { println!("(get-unsat-core)"); }
        if ctx.rng.gen_bool(0.3) && !ctx.all_assertions.is_empty() && (ctx.test_unsat_core || ctx.test_proof) {
            // try some check-sat-assuming with pairs
            let mut names = ctx.all_assertions.clone();
            names.shuffle(ctx.rng);
            for pair in names.chunks(2).take(3) {
                if pair.len() == 2 { println!("(check-sat-assuming ({} {}))", pair[0], pair[1]); }
            }
        }
        if ctx.rng.gen_bool(0.3) { println!("(pop 1)"); }
        if ctx.rng.gen_bool(0.1) { println!("(reset-assertions)"); }
    }
}

fn gen_ncnf(ctx: &mut Ctx, ratio: usize, cntsize: usize) {
    // Nested boolean structure with implications and equivalences
    let num_vars = (cntsize / ratio.max(1)).clamp(3, 128);
    for i in 0..num_vars { println!("(declare-const b{} Bool)", i); }
    let mut left = cntsize;
    while left > 0 {
        let e = random_bool_struct(num_vars, 0, ctx.rng);
        emit_assert(ctx, &e);
        left -= 1;
        maybe_midstream_check(ctx);
    }
}

fn random_bool_struct(num_vars: usize, depth: usize, rng: &mut StdRng) -> String {
    if depth > 3 || rng.gen_bool(0.25) {
        let v = rng.gen_range(0..num_vars);
        return if rng.gen_bool(0.5) { format!("b{}", v) } else { format!("(not b{})", v) };
    }
    let choice = rng.gen_range(0..4);
    match choice {
        0 => format!("(=> {} {})", random_bool_struct(num_vars, depth + 1, rng), random_bool_struct(num_vars, depth + 1, rng)),
        1 => format!("(= {} {})", random_bool_struct(num_vars, depth + 1, rng), random_bool_struct(num_vars, depth + 1, rng)),
        2 => format!("(and {} {})", random_bool_struct(num_vars, depth + 1, rng), random_bool_struct(num_vars, depth + 1, rng)),
        _ => format!("(or {} {})", random_bool_struct(num_vars, depth + 1, rng), random_bool_struct(num_vars, depth + 1, rng)),
    }
}

fn gen_cnfexp(ctx: &mut Ctx, ratio: usize, cntsize: usize) {
    // Like CNF but with extra auxiliary variables and equivalence-expanded definitions
    let num_clauses = cntsize.clamp(1, 2000);
    let num_vars = (num_clauses / ratio.max(1)).clamp(3, 200);
    for i in 0..num_vars { println!("(declare-const p{} Bool)", i); }
    let mut aux = 0usize;
    for _ in 0..num_clauses {
        let k = ctx.rng.gen_range(2..=5);
        let mut lits: Vec<String> = Vec::new();
        for _ in 0..k {
            let v = ctx.rng.gen_range(0..num_vars);
            let base = format!("p{}", v);
            let lit = if ctx.rng.gen_bool(0.5) { base } else { format!("(not {})", base) };
            lits.push(lit);
        }
        // Introduce an aux var equivalent to this clause
        println!("(declare-const a{} Bool)", aux);
        println!("(assert (= a{} (or {})))", aux, lits.join(" "));
        emit_assert(ctx, &format!("a{}", aux));
        aux += 1;
        maybe_midstream_check(ctx);
    }
}

fn gen_noinc_uf(ctx: &mut Ctx, cntsize: usize) {
    // declare a few uninterpreted sorts and functions over Int/BV/Bool
    let num_funs = (cntsize / 6).clamp(1, 8);
    let num_args_pool = [0, 1, 2, 3];
    let domains = ["Int", "Bool", "(_ BitVec 32)"];
    for i in 0..num_funs {
        let arity = *num_args_pool.choose(ctx.rng).unwrap();
        let mut sig = String::new();
        sig.push_str("(declare-fun f"); sig.push_str(&i.to_string()); sig.push(' ');
        if arity == 0 {
            sig.push_str("() Bool)");
        } else {
            sig.push('(');
            for a in 0..arity {
                if a > 0 { sig.push(' '); }
                sig.push_str(domains.choose(ctx.rng).unwrap());
            }
            sig.push_str(") Bool)");
        }
        println!("{}", sig);
    }
    // vars
    for i in 0..6 { println!("(declare-const i{} Int)", i); }
    for i in 0..6 { println!("(declare-const x{} (_ BitVec 32))", i); }
    for i in 0..6 { println!("(declare-const b{} Bool)", i); }

    let mut left = cntsize;
    while left > 0 {
        // build simple atoms using UF apps
        let app = random_uf_app(ctx);
        emit_assert(ctx, &app);
        if ctx.rng.gen_bool(0.2) { maybe_quantified_assert(ctx); }
        left -= 1;
        maybe_midstream_check(ctx);
    }
}

fn random_uf_app(ctx: &mut Ctx) -> String {
    // choose fN
    let upper = ctx.rng.gen_range(1..=6) + 1;
    let f = ctx.rng.gen_range(0..upper);
    let arity = ctx.rng.gen_range(0..=3);
    if arity == 0 { return format!("f{}", f); }
    let mut args = Vec::new();
    for _ in 0..arity {
        let choice = ctx.rng.gen_range(0..3);
        let a = match choice {
            0 => format!("i{}", ctx.rng.gen_range(0..6)),
            1 => format!("x{}", ctx.rng.gen_range(0..6)),
            _ => format!("b{}", ctx.rng.gen_range(0..6)),
        };
        args.push(a);
    }
    format!("(f{} {} )", f, args.join(" "))
}

fn maybe_quantified_assert(ctx: &mut Ctx) {
    // For QBF or non-QF logics, prefer quantifiers more often.
    let p = if ctx.test_qbf || ctx.prefer_quant_in_non_qf { 0.6 } else { 0.1 };
    if ctx.rng.gen_bool(p) {
        let use_real = ctx.has_real && ctx.rng.gen_bool(0.5);
        let sort = if use_real { "Real" } else { "Int" };
        let n = ctx.rng.gen_range(1..=2);
        let mut binders = Vec::new();
        for i in 0..n { binders.push(format!("(q{} {})", i, sort)); }
        let body = if use_real {
            format!("(=> (> q0 0.0) (>= (+ q0 {}) 0.0))", ctx.rng.gen_range(-3..=3))
        } else {
            format!("(=> (> q0 0) (>= (+ q0 {}) 0))", ctx.rng.gen_range(-3..=3))
        };
        emit_assert(ctx, &format!("(forall ({} ) {} )", binders.join(" "), body));
    }
}

fn maybe_quantified_assert_bv(ctx: &mut Ctx) {
    // Emit simple quantified BV constraints when non-QF logics are selected.
    // We stick to 32-bit since that's what BV variables use here.
    let p = if ctx.prefer_quant_in_non_qf { 0.6 } else { 0.1 };
    if ctx.rng.gen_bool(p) {
        let bw = 32usize;
        let n = ctx.rng.gen_range(1..=2);
        let mut binders = Vec::new();
        for i in 0..n { binders.push(format!("(qb{} (_ BitVec {}))", i, bw)); }
        // Build a small BV implication as the body
        let lit: u32 = ctx.rng.gen();
        let body = format!(
            "(=> (= (bvand qb0 (_ bv{} {})) (_ bv{} {})) (bvule (bvor qb0 (_ bv{} {})) (bvnot (_ bv0 {}))))",
            lit, bw, lit, bw, lit, bw, bw
        );
        emit_assert(ctx, &format!("(forall ({} ) {} )", binders.join(" "), body));
    }
}

fn gen_arrays(ctx: &mut Ctx, idx_bw: usize, elt_bw: usize, approx: usize) {
    // Generic array generation: declares a few arrays and emits select/store constraints.
    // idx_bw/elt_bw of 0 encode Int index/element; 32 encodes BitVec(32) index/element.
    let n = approx.clamp(1, 8);
    let idx_sort = if idx_bw == 0 { "Int".to_string() } else { format!("(_ BitVec {})", idx_bw) };
    let elt_sort = if elt_bw == 0 { "Int".to_string() } else if elt_bw == 3 { "String".to_string() } else { format!("(_ BitVec {})", elt_bw) };
    for i in 0..n { println!("(declare-const A{} (Array {} {}))", i, idx_sort, elt_sort); }
    // helper to emit an index literal
    let emit_idx = |rng: &mut StdRng| -> String {
        if idx_bw == 0 { format!("{}", rng.gen_range(-5..=5)) } else { format!("(_ bv{} {})", rng.gen::<u32>(), idx_bw) }
    };
    // element literal
    let emit_elt = |rng: &mut StdRng| -> String {
        if elt_bw == 0 { format!("{}", rng.gen_range(-10..=10)) } else if elt_bw == 3 { "\"e\"".to_string() } else { format!("(_ bv{} {})", rng.gen::<u32>(), elt_bw) }
    };
    for _ in 0..(approx * 2).clamp(2, 24) {
        let a = ctx.rng.gen_range(0..n);
        if ctx.rng.gen_bool(0.5) {
            // select equals element
            let i = emit_idx(ctx.rng);
            let v = emit_elt(ctx.rng);
            emit_assert(ctx, &format!("(= (select A{} {}) {} )", a, i, v));
        } else {
            // store then select
            let i1 = emit_idx(ctx.rng);
            let v1 = emit_elt(ctx.rng);
            let i2 = emit_idx(ctx.rng);
            let v2 = emit_elt(ctx.rng);
            let v1c = v1.clone();
            let rhs = if i1 == i2 { v1 } else { v2 };
            emit_assert(ctx, &format!("(= (select (store A{} {} {}) {}) {} )", a, i1, v1c, i2, rhs));
        }
        maybe_midstream_check(ctx);
    }
}


