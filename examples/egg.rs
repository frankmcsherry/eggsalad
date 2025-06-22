use eggsalad::egraph::{
    patterns::{Pattern, Symbol, Rewrite},
    EGraph,
};
use eggsalad::Function;

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Op {
    Add,
    Mul,
    Div,
    Shf,
    Lit(i32),
    Var(i32),
}

impl Function for Op {
    fn inputs(&self) -> usize {
        match self {
            Op::Add | Op::Mul | Op::Div | Op::Shf => 2,
            Op::Lit(_) | Op::Var(_) => 0,
        }
    }
}

pub mod constant_fold {

    use eggsalad::Function;
    use eggsalad::egraph::{EGraph, ENode, Searcher};
    use crate::Op;

    impl Op {
        pub fn eval(&self, args: &[&Op]) -> Option<Op> {
            println!("Eval: {:?} {:?}", self, args);
            if args.len() != self.inputs() {
                return None;
            } else {
                match self {
                    Op::Add => Some(Op::Lit(args[0].as_lit()? + args[1].as_lit()?)),
                    Op::Mul => Some(Op::Lit(args[0].as_lit()? * args[1].as_lit()?)),
                    Op::Div => Some(Op::Lit(args[0].as_lit()? / args[1].as_lit()?)),
                    Op::Shf => Some(Op::Lit(args[0].as_lit()? << args[1].as_lit()?)),
                    Op::Lit(_) | Op::Var(_) => None,
                }
            }
        }
        pub fn as_lit(&self) -> Option<i32> {
            if let Op::Lit(l) = self { Some(*l) }
            else { None }
        }
    }

    pub struct ConstantFold;

    impl Searcher<Op> for ConstantFold {
        fn search(&self, e_graph: &EGraph<Op>) -> Vec<(ENode<Op>, ENode<Op>)> {
            let mut results = Vec::new();
            for (_id, e_class) in e_graph.members.iter() {
                for e_node in e_class.iter() {
                    match e_node.op {
                        Op::Add | Op::Mul | Op::Div => {
                            // Each of these could seek to the contiguous range of literals, as they are sort by op.
                            let lits0 = e_graph.members[&e_node.args[0]].iter().filter(|x| x.op.as_lit().is_some());
                            let lits1 = e_graph.members[&e_node.args[1]].iter().filter(|x| x.op.as_lit().is_some());
                            for arg0 in lits0 {
                                for arg1 in lits1.clone() {
                                    if let Some(Op::Lit(new_lit)) = e_node.op.eval(&[&arg0.op, &arg1.op]) {
                                        let new_node = ENode::new(Op::Lit(new_lit), vec![]);
                                        results.push((e_node.clone(), new_node));
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            results
        }
    }

}

fn main() {
    let mut e_graph: EGraph<Op> = Default::default();

    let eggsample = vec![Op::Div, Op::Mul, Op::Var(0), Op::Lit(2), Op::Lit(2)];

    // (a x 2) / 2
    e_graph.insert(eggsample);

    let rewrites = vec![
        Rewrite {   // a x 2 -> a << 1 
            source: Pattern::new(vec![Symbol::Operator(Op::Mul), Symbol::Variable(0), Symbol::Operator(Op::Lit(2))]),
            target: Pattern::new(vec![Symbol::Operator(Op::Shf), Symbol::Variable(0), Symbol::Operator(Op::Lit(1))]),
        },
        Rewrite {   // a / a -> 1 
            source: Pattern::new(vec![Symbol::Operator(Op::Div), Symbol::Variable(0), Symbol::Variable(0)]),
            target: Pattern::new(vec![Symbol::Operator(Op::Lit(1))]),
        },
        Rewrite {   // a x 1 -> a 
            source: Pattern::new(vec![Symbol::Operator(Op::Mul), Symbol::Variable(0), Symbol::Operator(Op::Lit(1))]),
            target: Pattern::new(vec![Symbol::Variable(0)]),
        },
        Rewrite {   // (a x b) / c -> a x (b / c)
            source: Pattern::new(vec![Symbol::Operator(Op::Div), Symbol::Operator(Op::Mul), Symbol::Variable(0), Symbol::Variable(1), Symbol::Variable(2)]),
            target: Pattern::new(vec![Symbol::Operator(Op::Mul), Symbol::Variable(0), Symbol::Operator(Op::Div), Symbol::Variable(1), Symbol::Variable(2)]),
        },
    ];

    let mut saturated = false;
    while !saturated {
        for rewrite in rewrites.iter() {
            rewrite.apply(&mut e_graph);
        }
        saturated = !e_graph.refresh();
    }

    e_graph.refresh();
    println!("{}", e_graph);

    // println!("\nConstant Folding:");
    // for (source, target) in constant_fold::ConstantFold.search(&e_graph) {
    //     println!("{} -> {}", source, target);
    // }
}
