
pub trait TypeSystem<Term, Type> {
    type Context;
    fn infer(context: &mut Self::Context, term: &Term) -> Result<Type, String>;
}
