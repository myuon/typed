use crate::spec::*;
use crate::systems::simply::{Boolean, Context};

#[derive(Debug, Clone, PartialEq)]
pub enum Qualifier {
    // linear
    Lin,
    // unrestricted
    Un,
}

impl Qualifier {
    fn is_sub(&self, other: &Qualifier) -> bool {
        use self::Qualifier::*;

        match (self,other) {
            (_,Un) => true,
            (x,y) => x == y,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    VariableT(String),
    BooleanT(Qualifier, Boolean),
    IfT(Box<Term>, Box<Term>, Box<Term>),
    PairT(Qualifier, Box<Term>, Box<Term>),
    SplitT(Box<Term>, String, String, Box<Term>),
    LambdaT(Qualifier, String, Box<Type>, Box<Term>),
    ApplicationT(Box<Term>, Box<Term>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PreType {
    Bool,
    Pair(Box<Type>, Box<Type>),
    Function(Box<Type>, Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Type(Qualifier, Box<PreType>);

impl Type {
    fn get_qualifier(&self) -> Qualifier {
        self.0
    }

    fn get_pretype(&self) -> PreType {
        self.1.as_ref().clone()
    }

    fn can_qualify(&self, q: &Qualifier) -> bool {
        self.get_qualifier().is_sub(q)
    }
}

pub struct Linear {
}

impl TypeSystem<Term, Type> for Linear {
    type Context = Context<Type>;
    type Output = (Type, Context<Type>);

    fn infer(context: &mut Context<Type>, term: &Term) -> Result<Self::Output, String> {
        use self::Term::*;

        match term {
            VariableT(var) => {
                match context.find_var(var) {
                    None => Err(format!("Not found in context: {:?} in {:?}", var, context)),
                    Some(index) => {
                        let varType = context.get_at(index);
                        match varType.get_qualifier() {
                            Qualifier::Un => {
                                Ok((varType, Context::from_vec(context.as_vec())))
                            },
                            Qualifier::Lin => {
                                let mut vec = context.as_vec();
                                let head = vec[index];
                                vec.remove(index);
                                vec.insert(0, head);

                                Ok((varType, Context::from_vec(vec)))
                            },
                        }
                        
                    },
                }
            },
            BooleanT(q,b) => {
                Ok((
                    Type(q.clone(), Box::new(PreType::Bool)),
                    Context::from_vec(context.as_vec()),
                ))
            },
            IfT(t1,t2,t3) => {
                let (t1type, context2) = Self::infer(context, t1)?;
                if t1type.get_pretype() != PreType::Bool {
                    return Err(format!("Expected type (_ Bool), but got {:?}:{:?}", t1, t1type));
                }

                let t2out = Self::infer(&mut context2, t2)?;
                let t3out = Self::infer(&mut context2, t3)?;
                if t2out != t3out {
                    return Err(format!("Expected output {:?}, but got {:?}:{:?}", t2out, t3, t3out));
                }

                Ok(t2out)
            },
            PairT(q,t1,t2) => {
                let (t1type, context2) = Self::infer(context, t1)?;
                let (t2type, context3) = Self::infer(&mut context2, t2)?;
                if !t1type.can_qualify(q) {
                    return Err(format!("{:?} cannot qualify {:?}", t1type, q));
                }
                if !t2type.can_qualify(q) {
                    return Err(format!("{:?} cannot qualify {:?}", t2type, q));
                }

                Ok((
                    Type(q.clone(), Box::new(PreType::Pair(Box::new(t1type), Box::new(t2type)))),
                    context3,
                ))
            },
            SplitT(t1,x,y,t2) => {
                let (t1type, context2) = Self::infer(context, t1)?;
                let (t1type1, t1type2) = match t1type.get_pretype() {
                    PreType::Pair(t1type1, t1type2) => {
                        (t1type1,t1type2)
                    },
                    t => {
                        return Err(format!("Expected type _ * _, but got {:?}:{:?}", t1, t));
                    },
                };

                context2.cons(x.clone(), t1type1.as_ref().clone());
                context2.cons(y.clone(), t1type2.as_ref().clone());

                let (t2type, context3) = Self::infer(&mut context2, t2)?;

                Ok((
                    t2type,
                    context3,
                ))
            },
        }
    }
}
