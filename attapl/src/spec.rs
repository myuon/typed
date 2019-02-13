
pub trait TypeSystem<Term, Type> {
    type Context;
    type Output;
    fn infer(context: &mut Self::Context, term: &Term) -> Result<Self::Output, String>;
}
