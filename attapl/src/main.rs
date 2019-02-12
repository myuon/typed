#[macro_use] extern crate failure;

#[derive(Debug)]
enum Boolean {
    True,
    False,
}

#[derive(Debug)]
enum Term {
    VariableT(String),
    BooleanT(Boolean),
    IfT(Box<Term>, Box<Term>, Box<Term>),
    LambdaT(String, Box<Type>, Box<Term>),
    ApplicationT(Box<Term>, Box<Term>),
}

#[derive(Debug, PartialEq, Clone)]
enum Type {
    Bool,
    Function(Box<Type>, Box<Type>),
}

impl Type {
    fn is_function(&self) -> bool {
        use self::Type::*;

        match self {
            Function(_,_) => true,
            _ => false,
        }
    }
}

#[derive(Debug)]
struct Context(Vec<(String,Type)>);

impl Context {
    fn get(&self, var: &str) -> Option<Type> {
        self.0.iter().find(|p| p.0 == var).map(|p| p.1.clone())
    }

    fn cons(&mut self, var: String, typ: Type) {
        self.0.push((var,typ));
    }
}

fn infer(context: &mut Context, term: &Term) -> Result<Type, String> {
    use self::Term::*;

    match term {
        VariableT(var) => {
            match context.get(var) {
                None => Err(format!("Not found in context: {:?} in {:?}", var, context)),
                Some(t) => Ok(t),
            }
        },
        BooleanT(b) => Ok(Type::Bool),
        IfT(t1,t2,t3) => {
            let t1type = infer(context, t1)?;
            if t1type != Type::Bool {
                return Err(format!("Expected type Bool, but got {:?}:{:?}", t1, t1type));
            }

            let t2type = infer(context, t2)?;
            let t3type = infer(context, t3)?;
            if t2type != t3type {
                return Err(format!("Expected type {:?}, but got {:?}:{:?}", t2type, t3, t3type));
            }

            Ok(t2type)
        },
        LambdaT(var,typ,term) => {
            context.cons(var.clone(), typ.as_ref().clone());
            let typ2 = infer(context, term)?;

            Ok(Type::Function(typ.clone(), Box::new(typ2)))
        },
        ApplicationT(t1,t2) => {
            let t1type = infer(context, t1)?;
            match t1type {
                Type::Function(t1type1, t1type2) => {
                    let t2type = infer(context, t2)?;

                    if t1type1.as_ref() != &t2type {
                        return Err(format!("Expected type {:?}, but got {:?}:{:?}", t1type1, t2, t2type));
                    }

                    Ok(t1type2.as_ref().clone())
                },
                _ => {
                    Err(format!("Expected type (_ -> _), but got {:?}:{:?}", t1, t1type))
                },
            }
        },
    }
}

fn main() {
    let mut ctx = Context(vec![("x".to_string(), Type::Bool), ("y".to_string(), Type::Bool)]);
    let p = infer(&mut ctx, &Term::ApplicationT(
        Box::new(Term::LambdaT(
            "z".to_string(),
            Box::new(Type::Bool),
            Box::new(Term::VariableT("z".to_string())),
        )),
        Box::new(Term::VariableT("x".to_string()))
    ));

    println!("{:?}", p);
}
