extern crate attapl;

use attapl::*;
use attapl::simply::*;

#[test]
fn check_infer_lambda() {
    assert_eq!(
        Simply::infer(
            &mut Context::new(),
            &Term::LambdaT(
                "x".to_string(),
                Box::new(Type::Bool),
                Box::new(Term::VariableT("x".to_string())),
            )
        ),
        Ok(
            Type::Function(
                Box::new(Type::Bool),
                Box::new(Type::Bool),
            )
        ),
    );
}

#[test]
fn check_infer_context() {
    assert_eq!(
        Simply::infer(
            &mut Context::from_vec(vec![
                (
                    "f".to_string(),
                    Type::Function(
                        Box::new(Type::Function(
                            Box::new(Type::Bool),
                            Box::new(Type::Bool),
                        )),
                        Box::new(Type::Bool),
                    ),
                )
            ]),
            &Term::ApplicationT(
                Box::new(Term::VariableT("f".to_string())),
                Box::new(
                    Term::LambdaT(
                        "x".to_string(),
                        Box::new(Type::Bool),
                        Box::new(Term::VariableT("x".to_string())),
                    )
                ),
            )
        ),
        Ok(
            Type::Bool
        ),
    );
}
