## What changed

Proved `WeilConjectures.IntegralSystemRealization.IndependentExpression.pointwiseShift_component`
without changing its statement or any existing definition. Added the private proof import
`Mathlib.CategoryTheory.Comma.Arrow` and proved private helpers for the context search,
evaluation of identity component arrows, evaluation of a map supported in one input, and
transport of isomorphism components along equalities of functors.
Bundled-arrow equality retains both endpoints throughout the expression induction. At tensor
vertices, injectivity of occurrence labels makes the other subtree an identity map. Mathlib's
`Functor.mapArrow` transports these equations through each primitive operation. Finally,
`Arrow.mk` removes the explicit endpoint equality transports and is injective at fixed endpoints.
Updated the item's proof record to describe this implementation of its existing induction plan.
The map lemma only requires injectivity of occurrence labels; existing surjectivity supplies the
actual context. The argument works for arbitrary integer shifts, including zero and negative
shifts, and does not add a finiteness assumption on the input-label type.

Searches: LeanFinder for a product-category functor's map in a single slot returned single-term
complex results, rather than an expression-context theorem. Loogle found
`CategoryTheory.Functor.congr_hom`; direct Mathlib inspection also found `Functor.mapArrow`,
`Arrow.mk_injective`, and the two lemmas removing `eqToHom` from bundled arrows. Repository
search found no existing expression-context map theorem. The existing occurrence definitions
and explicit context search are used unchanged.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralSystemRealization.IndependentExpression.pointwiseShift_component`
(node `lem-pur-independent-expression-reduction-shift`). No holes added or split off. No `sorry`
remains in the item module. All new private helpers are proved.

## No longer needed

None. The existing public import is retained because the file's original declarations and local
attributes use its interface. The proof uses the existing occurrence definition dependency and
Mathlib's arrow-category API. No dependency, module, or unit route is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The plan's identification of an insertion functor with the context is
implemented directly at the level of bundled arrows, avoiding a separate insertion construction
and functor equality. The node's proof and proof_origin now describe this argument.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
