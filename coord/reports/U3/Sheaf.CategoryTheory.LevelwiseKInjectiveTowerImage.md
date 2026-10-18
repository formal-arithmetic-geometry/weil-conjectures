## What changed

Proved `CategoryTheory.Functor.levelwiseKInjectiveTowerImage` in
`Sheaf.CategoryTheory.LevelwiseKInjectiveTowerImage`, with every existing public
signature and definition unchanged. Added the proof-only import
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` for the recorded
K-injective quasi-isomorphism/homotopy-equivalence criterion.

The proof implements the existing six-step route. Exact evaluation gives
quasi-isomorphisms at each level; the existing
`CategoryTheory.tower_evaluation_isKInjective` gives K-injectivity of the
resolution's evaluations. Mathlib's `CochainComplex.IsKInjective.quasiIso_iff`
and `Functor.mapHomotopyEquiv` show that applying the additive functor preserves
these particular quasi-isomorphisms. The evaluation criterion then gives the
quasi-isomorphism of strict towers. Applying the functor to the naturality square
gives the strict-transition compatibility.

A proved private helper transports naturality of the recorded derived unit
through `DerivedCategory.quotientCompQhIso`. At a K-injective resolution, the
existing `rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso` makes the comparison
invertible. Its naturality square and the two localized quasi-isomorphisms then
make the original comparison invertible. A second proved private helper checks
that functors preserve finite composites in `Functor.OfSequence.map`; applying
it to the opposite functor proves the literal constant-tower equality, including
all transition maps.

Read the cited source passages: Stacks `sites-cohomology.tex`,
`lemma-derived-limit-is-ok` (Tag 0941), exact-left-adjoint evaluation paragraph;
and `derived.tex`, `lemma-K-injective`, `lemma-K-injective-defined`, and
`lemma-enough-K-injectives-implies` (Tags 070I, 070Y, 070K).
The proof keeps these arguments and does not require compatible choices of
levelwise homotopy inverses or exactness of G.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Functor.levelwiseKInjectiveTowerImage`
(node `lem-sp-levelwise-kinjective-tower-image`).

Holes closed: 1. Holes added: 0. Split-offs: 0.
No `sorry` remains in the delivered module, including its two private helpers.
This is a proof from the existing recorded dependencies, including the still
unproved derived-unit computation theorem; it does not claim to close those
separate dependency obligations.

The complete file compiled without errors or warnings through `lcompile.py`.
Every line has at most 100 characters. No new axioms, definitions, or statements
with deferred proofs were introduced.

## No longer needed

None. No imports, nodes, or modules were pruned. All existing proof dependencies
remain used: levelwise abelianness through Mathlib's evaluation criterion,
evaluation K-injectivity through the upstream theorem, K-injective homotopy
comparison through the recorded Mathlib criterion, additivity through
`mapHomotopyEquiv`, the derived-category localization, and the recorded right
derived functor and unit. No change to the DAG route or unit route is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect found. Mathlib's complex-valued functor and
its functorial packaging required explicit local K-injective instance types and
unfolding in the transition-square proof; these are elaboration details only.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
