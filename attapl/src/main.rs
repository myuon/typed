extern crate attapl;

use attapl::*;
use attapl::simply::*;

fn main() {
    let mut ctx = Context(vec![("x".to_string(), Type::Bool), ("y".to_string(), Type::Bool)]);
    let p = Simply::infer(&mut ctx, &Term::ApplicationT(
        Box::new(Term::LambdaT(
            "z".to_string(),
            Box::new(Type::Bool),
            Box::new(Term::VariableT("z".to_string())),
        )),
        Box::new(Term::VariableT("x".to_string()))
    ));

    println!("{:?}", p);
}
