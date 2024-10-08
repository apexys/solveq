use egg::*;

pub type Constant = i64;

define_language! {
    enum EquationSystemLanguage{
        "pi" = Pi,
        "e" = E,
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "sqrt" = Sqrt(Id),
        "sin" = Sin(Id),
        "cos" = Cos(Id),
        "eq" = Eq([Id; 2]),
        "system" = System([Id; 2]),
        Constant(Constant),
        Symbol(Symbol),
    }
}


fn is_not_zero(var: &str) -> impl Fn(&mut EGraph<EquationSystemLanguage,ConstantFold>, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        let nodes =  &egraph[subst[var]].nodes;
        nodes != &[EquationSystemLanguage::Constant(0)]
    }
}

#[derive(Default)]
pub struct ConstantFold;
impl Analysis<EquationSystemLanguage> for ConstantFold {
    type Data = Option<(Constant, PatternAst<EquationSystemLanguage>)>;

    fn make(egraph: &EGraph<EquationSystemLanguage, ConstantFold>, enode: &EquationSystemLanguage) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            EquationSystemLanguage::Constant(c) => (*c, format!("{}", c).parse().unwrap()),
            EquationSystemLanguage::Add([a, b]) => (
                x(a)? + x(b)?,
                format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            EquationSystemLanguage::Sub([a, b]) => (
                x(a)? - x(b)?,
                format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            EquationSystemLanguage::Mul([a, b]) => (
                x(a)? * x(b)?,
                format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            EquationSystemLanguage::Div([a, b]) if x(b) != Some(0) && (x(a).and_then(|a| x(b).map(|b| a % b)) == Some(0)) => (
                x(a)? / x(b)?,
                format!("(/ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph<EquationSystemLanguage, ConstantFold>, id: Id) {
        let data = egraph[id].data.clone();
        if let Some((c, pat)) = data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(EquationSystemLanguage::Constant(c));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

fn make_rules() -> Vec<Rewrite<EquationSystemLanguage, ConstantFold>>{
    vec![
        //Normal expression
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("neutral-add"; "(+ ?a 0)" => "?a"),
        rewrite!("neutral-mul"; "(* ?a 1)" => "?a"),
        rewrite!("zero-mul"; "(* ?a 0)" => "0"),
        rewrite!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rewrite!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rewrite!("cancel-sub"; "(- ?a ?a)" => "0"),
        rewrite!("cancel-div"; "(/ ?a ?a)" => "1" if is_not_zero("?a")),
        rewrite!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
        rewrite!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
    ]
}


fn main() {
    let expr_str = "(+ (- 3 1) 3)";
    let expr: RecExpr<EquationSystemLanguage> = expr_str.parse().unwrap();
    let runner = Runner::default().with_expr(&expr).run(&make_rules());
    let extractor = Extractor::new(&runner.egraph, AstDepth);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    eprintln!("Expr: {} => {}", expr, best_expr);
}
