extern crate attapl;

use attapl::*;
use attapl::linear::*;

#[test]
fn check_infer_fail_discard() {
    let type_t = Type(
        Qualifier::Un,
        Box::new(PreType::Function(
            Box::new(Type(Qualifier::Un, Box::new(PreType::Bool))),
            Box::new(Type(Qualifier::Lin, Box::new(PreType::Bool))),
        ))
    );

    assert_eq!(
        Linear::infer(
            &mut Context::new(),
            &Term::LambdaT(
                Qualifier::Lin,
                "x".to_string(),
                Box::new(Type(Qualifier::Lin, Box::new(PreType::Bool))),
                Box::new(
                    Term::ApplicationT(
                        Box::new(Term::LambdaT(
                            Qualifier::Lin,
                            "f".to_string(),
                            Box::new(type_t.clone()),
                            Box::new(Term::BooleanT(Qualifier::Lin, Boolean::True)),
                        )),
                        Box::new(Term::LambdaT(
                            Qualifier::Un,
                            "y".to_string(),
                            Box::new(Type(Qualifier::Un, Box::new(PreType::Bool))),
                            Box::new(Term::VariableT("x".to_string())),
                        )),
                    )
                )
            )
        ).is_err(),
        true,
    );
}

#[test]
fn check_infer_fail_duplicate() {
    let type_t = Type(
        Qualifier::Un,
        Box::new(PreType::Function(
            Box::new(Type(Qualifier::Un, Box::new(PreType::Bool))),
            Box::new(Type(Qualifier::Lin, Box::new(PreType::Bool))),
        ))
    );

    assert_eq!(
        Linear::infer(
            &mut Context::new(),
            &Term::LambdaT(
                Qualifier::Lin,
                "x".to_string(),
                Box::new(Type(Qualifier::Lin, Box::new(PreType::Bool))),
                Box::new(
                    Term::ApplicationT(
                        Box::new(Term::LambdaT(
                            Qualifier::Lin,
                            "f".to_string(),
                            Box::new(type_t.clone()),
                            Box::new(Term::PairT(
                                Qualifier::Lin,
                                Box::new(
                                    Term::ApplicationT(
                                        Box::new(Term::VariableT("f".to_string())),
                                        Box::new(Term::BooleanT(Qualifier::Un, Boolean::True)),
                                    ),
                                ),
                                Box::new(
                                    Term::ApplicationT(
                                        Box::new(Term::VariableT("f".to_string())),
                                        Box::new(Term::BooleanT(Qualifier::Un, Boolean::True)),
                                    ),
                                ),
                            ))
                        )),
                        Box::new(Term::LambdaT(
                            Qualifier::Un,
                            "y".to_string(),
                            Box::new(Type(Qualifier::Un, Box::new(PreType::Bool))),
                            Box::new(Term::VariableT("x".to_string())),
                        )),
                    )
                )
            )
        ).is_err(),
        true,
    );
}
