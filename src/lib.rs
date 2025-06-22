pub mod egraph;

/// A type that requires inputs and produces an output.
pub trait Function {
    /// The number of inputs the function requires.
    fn inputs(&self) -> usize;
}

/// A type that requires inputs and produces outputs.
pub trait MultiFunction {
    /// The number of inputs the function requires.
    fn inputs(&self) -> usize;
    /// The number of outputs the function produces.
    fn outputs(&self) -> usize;
}

impl<F: Function> MultiFunction for F {
    fn inputs(&self) -> usize {
        Function::inputs(self)
    }
    fn outputs(&self) -> usize {
        1
    }
}

#[derive(Clone, Debug)]
pub struct Tree<T> {
    function: T,
    children: Vec<Tree<T>>,
}

impl<T: Function> Tree<T> {
    /// Create a new tree node, validating that the inputs are correct in number.
    pub fn new(function: T, children: Vec<Tree<T>>) -> Option<Self> {
        if children.len() == function.inputs() {
            Some(Tree { function, children })
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub struct Flat<T> {
    /// pre-order traversal
    functions: Vec<T>,
    /// Number of required inputs.
    inputs: usize,
    /// Number of produced outputs.
    outputs: usize,
}

impl<T: Function> From<Flat<T>> for Tree<T> {
    fn from(mut flat: Flat<T>) -> Self {
        let mut pending = Vec::new();
        while let Some(function) = flat.functions.pop() {
            let inputs = function.inputs();
            let mut children = pending.split_off(pending.len() - inputs);
            children.reverse();
            pending.push(Tree { function, children });
        }
        pending.pop().unwrap()
    }
}

impl<T> From<Tree<T>> for Flat<T> {
    fn from(tree: Tree<T>) -> Self {
        let mut flat = Flat::default();
        let mut todo = vec![tree];
        while let Some(node) = todo.pop() {
            flat.functions.push(node.function);
            todo.extend(node.children.into_iter().rev());
        }
        flat.inputs = 0;
        flat.outputs = 1;
        flat
    }
}

impl<T: MultiFunction> From<Vec<T>> for Flat<T> {
    fn from(functions: Vec<T>) -> Self {
        // We need to assess the number of required inputs and produced outputs.
        let mut inputs = 0;
        let mut outputs = 0;
        for function in functions.iter().rev() {
            if outputs < function.inputs() {
                inputs += function.inputs() - outputs;
                outputs = function.inputs();
            }
            outputs += function.outputs();
            outputs -= function.inputs();
        }
        Self {
            functions,
            inputs,
            outputs,
        }
    }
}

impl<T> Default for Flat<T> {
    fn default() -> Self {
        Flat {
            functions: Vec::new(),
            inputs: 0,
            outputs: 0,
        }
    }
}
