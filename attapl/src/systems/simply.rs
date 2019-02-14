use crate::spec::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Boolean {
    True,
    False,
}

#[derive(Debug)]
pub enum Term {
    VariableT(String),
    BooleanT(Boolean),
    IfT(Box<Term>, Box<Term>, Box<Term>),
    LambdaT(String, Box<Type>, Box<Term>),
    ApplicationT(Box<Term>, Box<Term>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Bool,
    Function(Box<Type>, Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Context<Type>(pub Vec<(String,Type)>);

impl<Type: Clone> Context<Type> {
    pub fn new() -> Context<Type> {
        Context(vec![])
    }

    pub fn from_vec(vec: Vec<(String,Type)>) -> Context<Type> {
        Context(vec)
    }

    fn get(&self, var: &str) -> Option<Type> {
        self.0.iter().find(|p| p.0 == var).map(|p| p.1.clone())
    }

    pub fn get_at(&self, index: usize) -> Type {
        self.0[index].1.clone()
    }

    pub fn cons(&mut self, var: String, typ: Type) {
        self.0.push((var,typ));
    }

    pub fn as_vec(&self) -> Vec<(String, Type)> {
        self.0.clone()
    }

    pub fn find_var(&self, var: &str) -> Option<usize> {
        self.0.iter().position(|p| p.0 == var)
    }
}

pub struct Simply {
}

impl Simply {
    pub fn new() -> Simply {
        Simply {
        }
    }
}

impl TypeSystem<Term, Type> for Simply {
    type Context = Context<Type>;
    type Output = Type;

    fn infer(context: &mut Context<Type>, term: &Term) -> Result<Type, String> {
        use self::Term::*;

        match term {
            VariableT(var) => {
                match context.get(var) {
                    None => Err(format!("Not found in context: {:?} in {:?}", var, context)),
                    Some(t) => Ok(t),
                }
            },
            BooleanT(_) => Ok(Type::Bool),
            IfT(t1,t2,t3) => {
                let t1type = Self::infer(context, t1)?;
                if t1type != Type::Bool {
                    return Err(format!("Expected type Bool, but got {:?}:{:?}", t1, t1type));
                }

                let t2type = Self::infer(context, t2)?;
                let t3type = Self::infer(context, t3)?;
                if t2type != t3type {
                    return Err(format!("Expected type {:?}, but got {:?}:{:?}", t2type, t3, t3type));
                }

                Ok(t2type)
            },
            LambdaT(var,typ,term) => {
                context.cons(var.clone(), typ.as_ref().clone());
                let typ2 = Self::infer(context, term)?;

                Ok(Type::Function(typ.clone(), Box::new(typ2)))
            },
            ApplicationT(t1,t2) => {
                let t1type = Self::infer(context, t1)?;
                match t1type {
                    Type::Function(t1type1, t1type2) => {
                        let t2type = Self::infer(context, t2)?;

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
}

