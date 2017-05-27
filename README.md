# Typed

Based on [TaPL](https://www.amazon.co.jp/dp/B00AJXZ5JE/ref=dp-kindle-redirect?_encoding=UTF8&btkr=1)

- Expr
  - [Arith](src/Expr/Arith.hs): Arithmetic Expression (bool, nat)
- Lambda 
  - Explicit: explicit type annotation (no unification)
	- [Untyped](src/Lambda/Explicit/Untyped.hs): Untyped Lambda Calculus
	- [Simply](src/Lambda/Explicit/Simply.hs): Simply Typed (AExp, function)
	- [SimplyExt](src/Lambda/Explicit/SimplyExt.hs): Extended Simply; explicit typed (additional base, unit, tuple, record, sum, variant, polymorphic list)
	- [Reference](src/Lambda/Explicit/Reference.hs): Reference with Simply typed
	- [Exception](src/Lambda/Explicit/Exception.hs): Exception with Simply typed
	- [Subtyping](src/Lambda/Explicit/Subtyping.hs): Subtyping with Simply typed
	- [Recursive](src/Lambda/Explicit/Recursive.hs): Recursive type with Simply typed 
