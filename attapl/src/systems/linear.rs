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
        self.0.clone()
    }

    fn get_pretype(&self) -> PreType {
        self.1.as_ref().clone()
    }

    fn can_qualify(&self, q: &Qualifier) -> bool {
        self.get_qualifier().is_sub(q)
    }
}

fn divides(this: &Context<Type>, mut other: Context<Type>) -> Result<Context<Type>, String> {
    match other.0.pop() {
        None => Ok(this.clone()),
        Some((x,xtype)) => {
            match xtype.get_qualifier() {
                Qualifier::Lin => {
                    let context = divides(this, other)?;
                    if context.0.iter().any(|p| *p == (x.clone(),xtype.clone())) {
                        return Err(format!("{:?} should not have {:?}:{:?}", context, x, xtype));
                    }
                    
                    Ok(context)
                },
                Qualifier::Un => {
                    let context = divides(this, other)?;
                    if !context.0.iter().any(|p| *p == (x.clone(),xtype.clone())) {
                        return Err(format!("{:?} should have {:?}:{:?}", context, x, xtype));
                    }

                    Ok(context)
                },
            }
        },
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
                                let head = vec[index].clone();
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
                let (t1type, mut context2) = Self::infer(context, t1)?;
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
                let (t1type, mut context2) = Self::infer(context, t1)?;
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
                let (t1type, mut context2) = Self::infer(context, t1)?;
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
                let context4 = divides(&context3, Context::from_vec(vec![ (x.clone(), t1type1.as_ref().clone()), (y.clone(), t1type2.as_ref().clone()) ]))?;

                Ok((
                    t2type,
                    context4,
                ))
            },
            LambdaT(q,x,typ1,t2) => {
                context.cons(x.clone(), typ1.as_ref().clone());
                let (t2typ, context2) = Self::infer(context, t2)?;
                let context3 = divides(&context2, Context::from_vec(vec![ (x.clone(), typ1.as_ref().clone()) ]))?;

                if *q == Qualifier::Un && *context != context3 {
                    return Err(format!("Expected {:?}, but got {:?}", context, context3));
                }

                Ok((
                    Type(q.clone(), Box::new(PreType::Function( Box::new(typ1.as_ref().clone()), Box::new(t2typ) ))),
                    context3
                ))
            },
            ApplicationT(t1,t2) => {
                let (t1type, context2) = Self::infer(context, t1)?;
                match t1type.get_pretype() {
                    PreType::Function(t1type1, t1type2) => {
                        let (t2type, context3) = Self::infer(context, t2)?;

                        if *t1type1.as_ref() != t2type {
                            return Err(format!("Expected type {:?}, but got {:?}:{:?}", t1type1, t2, t2type));
                        }

                        Ok((
                            t1type2.as_ref().clone(),
                            context3,
                        ))
                    },
                    _ => {
                        Err(format!("Expected type (_ -> _), but got {:?}:{:?}", t1, t1type))
                    },
                }
            },
        }
    }
}
