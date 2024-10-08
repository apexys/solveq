use std::{collections::HashMap, env::var};

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
        "eq" = Eq([Id; 2]), //Equation type (eq expr1 expr2)
        "system" = System(Box<[Id]>), //System can contain itself to make a list. The leaves should be eq or empty
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

fn is_symbol(var: &str) -> impl Fn(&mut EGraph<EquationSystemLanguage,ConstantFold>, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        let nodes =  &egraph[subst[var]].nodes;
        matches!(nodes[0], EquationSystemLanguage::Symbol(_))
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
        //rewrite!("sub-to-add"; "(- ?a ?b)" => "(+ ?a (- 0 ?b))"),
        //rewrite!("div-to-mul"; "(/ ?a ?b)" => "(* ?a (/ 1 ?b))"),

        //Fractions
        //rewrite!("fraction-base-one"; "?a" => "(/ ?a 1)"),
        //rewrite!("add-two-fractions"; "(+ (/ ?a ?b) (/ ?c ?d))" => "(+ (/ (* ?a ?d) (* ?b ?d)) (/ (* ?c ?d) (* ?b ?d)))"),
        //rewrite!("sub-two-fractions"; "(- (/ ?a ?b) (/ ?c ?d))" => "(- (/ (* ?a ?d) (* ?b ?d)) (/ (* ?c ?d) (* ?b ?d)))"),
        rewrite!("mul-two-fractions"; "(* (/ ?a ?b) (/ ?c ?d))" => "(/ (* ?a ?c) (* ?b ?d))"),
        rewrite!("div-two-fractions"; "(/ (/ ?a ?b) (/ ?c ?d))" => "(* (/ ?a ?c) (/ ?d ?b))"),

        //Equations
        rewrite!("commute-eq"; "(eq ?a ?b)" => "(eq ?b ?a)"),
        rewrite!("solve-multiplication-left"; "(eq (* ?a ?b) ?c)" => "(eq ?a (/ ?c ?b))"),
        rewrite!("solve-division-left"; "(eq (/ ?a ?b) ?c)" => "(eq ?a (* ?c ?b))"),
        rewrite!("solve-addition-left"; "(eq (+ ?a ?b) ?c)" => "(eq ?a (- ?c ?b))"),
        rewrite!("solve-subtraction-left"; "(eq (- ?a ?b) ?c)" => "(eq ?a (+ ?c ?b))"),
        rewrite!("solve-subtraction-right"; "(eq ?a (- ?b ?c))" => "(eq ?b (+ ?a ?c))"),
        rewrite!("solve-addition-right"; "(eq ?a (+ ?b ?c))" => "(eq ?b (- ?a ?c))"),
        //rewrite!("solve-self-division"; "(eq ?a ?b)" => "(eq 1 (/ ?b ?a))"),
        rewrite!("solve-two-vars"; "(eq ?a ?b)" => "(eq (/ ?b ?a) 1)" if is_symbol("?a"))
    ]
}


struct ExtractVariableCostFunction<'a>{
    variable: Symbol,
    graph: &'a EGraph<EquationSystemLanguage, ConstantFold>,
    minimal_symbol_depths: HashMap<Id, f64>,
}

impl<'a> ExtractVariableCostFunction<'a> {
    pub fn new(graph: &'a EGraph<EquationSystemLanguage, ConstantFold>, variable: Symbol) -> Self{
        Self { variable, graph, minimal_symbol_depths: Default::default() }
    }

    fn depth_cost_for_id(&mut self, id: Id) -> f64{
        if let Some(depth) = self.minimal_symbol_depths.get(&id).copied(){
            depth
        }else{
            let depth = self.graph[id].iter().filter(|variant| {
                !variant.children().contains(&id)
            }).map(|variant|{
                self.symbol_depth_cost(variant)
            } ).min_by(f64::total_cmp).unwrap_or_default();
            self.minimal_symbol_depths.insert(id, depth);
            depth
        }

    }

    fn symbol_depth_cost(&mut self, l: &EquationSystemLanguage) -> f64 { 
        match l{
            EquationSystemLanguage::Constant(_) |
            EquationSystemLanguage::Pi |
            EquationSystemLanguage::E => 0.0,
            EquationSystemLanguage::Symbol(global_symbol) => {
                if *global_symbol == self.variable{
                    1.0
                }else{
                    0.0
                }
            },
            other => {
                let mut result = 0.0;
                for c in other.children(){
                    result += self.depth_cost_for_id(*c);
                }
                if result > 0.0{
                    result + 1.0
                }else{
                    0.0
                }
            }           
        }
    }
}



impl<'a> CostFunction<EquationSystemLanguage> for ExtractVariableCostFunction<'a>{
    type Cost = f64;

    fn cost<C>(&mut self, enode: &EquationSystemLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost {

        // Left: Var = 0, other = 2
        // Right: Var = 100, other = 1
        match enode {
            EquationSystemLanguage::Eq([left, right]) => {
                enode.fold(1.0, |sum,id| {
                    sum + (if id == *left{
                        let left_subtree = &self.graph[id];
                        let left_id_count = left_subtree.leaves().filter(|l| **l == EquationSystemLanguage::Symbol(self.variable)).count();
                        (costs(id) * 2.0) + match left_id_count{
                            0 => 100.0,
                            1 => 0.0,
                            n => (n as f64) * 2.0 //Get rid of extra variables on the left side
                        }
                    }else if id == *right{
                        let right_subtree = &self.graph[id];
                        let right_contains_id = right_subtree.leaves().any(|l| *l == EquationSystemLanguage::Symbol(self.variable));
                        costs(id) + if right_contains_id {1000.0} else { 0.0 }
                    }else{
                        panic!("Weird else!");
                    })
                }) + (self.symbol_depth_cost(enode) * 2.0 )
            },
            _ => {
                enode.fold(1.0, |sum, id| (sum + costs(id)))
            },
        }
    }
}

fn main() {


    let expr_str = "(eq (/ x 2) (+ (+ 48 x) 4))";
    //let expr_str = "(eq (- (/ x 2) x) 52)";
    let expr: RecExpr<EquationSystemLanguage> = expr_str.parse().unwrap();
    let variable = Symbol::from("x");
    let runner = Runner::default().with_expr(&expr).run(&make_rules());
    let cost_function = ExtractVariableCostFunction::new(&runner.egraph, variable);
    let extractor = Extractor::new(&runner.egraph, cost_function);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    eprintln!("Expr: {} => {}", expr, best_expr);

    /*let left: RecExpr<EquationSystemLanguage> = "(/ x 2)".parse().unwrap();
    let right: RecExpr<EquationSystemLanguage> = "(+ (+ 48 x) 4))".parse().unwrap();
    let variable: RecExpr<EquationSystemLanguage> = "x".parse().unwrap();
    let mut runner = Runner::default();
    //let root = runner.roots[0];
    let left_id = runner.egraph.add_expr(&left);
    let right_id = runner.egraph.add_expr(&right);
    runner.egraph.union(left_id, right_id);
    runner.egraph.rebuild();
    runner = runner.run(&make_rules());
    let class_id = runner.egraph.lookup_expr(&variable).unwrap();
    let extractor = Extractor::new(&runner.egraph, AstDepth);
    let (best_cost, best_expr) = extractor.find_best(class_id);
    eprintln!("Expr: {}", best_expr);*/
}
