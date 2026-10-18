## What changed

Proved `AlgebraicGeometry.Etale.rGamma_unbounded_bounded` in
`Sheaf.AlgebraicGeometry.RGammaUnboundedBounded`, retaining its exact statement.
Three proved private helpers transfer the Mathlib K-injective Hom bijection through
`quotientCompQhIso`, and map homotopies through an additive functor.

The comparison lifts `(Qa)⁻¹ ≫ Qb`; cancellation gives augmentation compatibility and
uniqueness. Lifting the inverse gives both inverse homotopies. Their images under
sections provide an explicit inverse in the derived category. The source API
`Functor.rightDerivedFunctorObjQIso` computes RΓ on I; composing with the comparison
provides the compatible computation on J. The final naturality square follows by
cancelling Qa, reflecting equality to a homotopy into J′, and applying sections.

Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`.
Updated the existing node's proof, proof dependencies and proof origin to match.
A declaration-scoped unused-variable linter setting preserves the original nested
`eC′` binder, which is unused in the result of that quantifier. Public imports,
signatures and definitions are unchanged; no consumer adaptation is needed.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.rGamma_unbounded_bounded`
(node `lem-kun-rgamma-unbounded-bounded`). Added 0 holes and 0 split-offs.
There are no remaining `sorry` declarations in this delivery.

The remote single-file compile succeeds. `#print axioms` for the theorem reports
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`: the theorem already receives
  both resolutions, so resolution existence and a functorial replacement are unused.
  Removed the proof dependency and top-level tool approval for
  `prop-weil-pbc-kinjective-resolutions-exist`.
- `Sheaf.CategoryTheory.RingedSiteModules`: its general ringed-site abbreviation is
  unused; the statement's module-valued sheaves and sections already have their
  public interfaces. Removed the proof dependency and top-level tool approval for
  `def-weil-sheaf-of-modules-category`. Its statement dependency remains intact.

The other declared proof dependencies are retained. The unit record has no realized
statement or proof steps for this auxiliary lemma; the unit route is unchanged.
No modules are withdrawn, and no claim is made that the removed modules are globally
unreachable from other consumers.

## Where the brief, the DAG or earlier work was wrong

The planned initial choice of resolutions was redundant for the actual Lean
statement, which already quantifies over them and assumes their properties.
No mathematical statement or definition needed repair.

Read the Mathlib K-injective Hom bijection and quotient/homotopy APIs, the source
right-derived-functor computation API, the current blueprint lemma and unit, and
Stacks `derived.tex`, `lemma-K-injective` (Tag 070I). Search used LeanFinder,
Loogle and grep through `msearch.py`, and direct repository/Mathlib searches.
The general Hom bijection and existing derived-computation API give the complete
proof without any new mathematical obligations. Zero complexes, the zero ring,
and arbitrary bounds are covered by the same argument: it uses no degree bound,
nonzero hypothesis, boundedness of I or J, or injectivity of individual terms.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
