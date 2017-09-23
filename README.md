# Typed

## Implementation

Based on [TaPL](https://www.amazon.co.jp/dp/B00AJXZ5JE/ref=dp-kindle-redirect?_encoding=UTF8&btkr=1)

- Preliminaries
  - [Preliminaries](src/Preliminaties.hs): Preliminaries
- Untyped
  - [Arith](src/Untyped/Arith.hs): Arithmetic Expression (bool, nat)
  - [Untyped](src/Untyped/Untyped.hs): Untyped Lambda Calculus (with de Bruijn index)
- Typed
  - [Arith](src/Typed/Arith.hs): Arithmetic Expression (bool, nat)
  - [Simply](src/Typed/Simply.hs): Simply Typed (with explicit type annotation)
  - [SimplyExt](src/Typed/SimplyExt.hs): Extended Simply; base, unit, tuple, record, sum, variant, polymorphic list type (with explicit type annotation)
  - [Reference](src/Typed/Reference.hs): Simply + Reference type
  - [Exception](src/Typed/Exception.hs): Simply + Exception type

## Proofs

- Untyped
  - [Lambda.thy](theory/Lambda.thy): Untyped Lambda Calculus (beta reduction, fixedpoint, definability, Church-Rosser)
- Typed
  - [Simply.thy](theory/Simply.thy): Simply Typed Lambda Calculus
