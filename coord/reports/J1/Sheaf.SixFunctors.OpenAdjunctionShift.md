## What changed

Proved `WeilConjectures.IntegralSystemRealization.openAdjunctionShift` in
`Sheaf.SixFunctors.OpenAdjunctionShift`, with its signature and both fixed shift
structures unchanged. Added a proof-only import of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift`
for its proved cochain-unit compatibility instance. The derived unit, after
precomposition with Q, is explicitly identified with the localized cochain unit
and the exact-functor factorization inverses. All factors commute with shifts;
essential surjectivity descends this fact, and `Adjunction.CommShift.mk'` gives
both unit and counit compatibility. Updated the existing node's proof and dependencies.

Validation: the final module compiles cleanly through lcompile.py (7.2 seconds
on resumption).
Import-direction check permits the new proof import. No new declarations,
definitions, axioms, assumptions, or statement changes. The argument works for
identity and empty opens and for zero and negative shifts, because the generic
cochain-unit instance and descent work for every exact ordinary adjunction and
all integer shifts.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.IntegralSystemRealization.openAdjunctionShift`
(node `lem-pur-open-adjunction-shift`). Holes closed: 1. Holes added: 0.
No sorry remains in the delivered module. No split-off statements.
Existing dependencies' holes are unchanged.

## No longer needed

Removed the proof-only imports:
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Sheaf.Paper.CoefficientRingedSequenceSite`

The proof no longer needs the reconstruction dependencies
`lem-pur-site-restriction-module-adjunction-exact`,
`def-coef-ringed-sequence-site`, `def-weil-extension-by-zero-presheaf`,
`def-weil-presheaf-modules-sheafification`, or `def-pc-sheaf-restrict-scalars`:
`Open` already stores the exact ordinary adjunction whose localization is
`Open.adj`. Removed the obsolete localized-site tool-use approval from this
node. The public imports are retained as the existing statement interface;
no assertion is made that their modules are globally unreachable. In particular,
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems` stays publicly imported,
but its exactness theorem is not invoked by this proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was needed. The original plan redundantly
reconstructed the ordinary adjunction that the `Open` structure already stores.
The general upstream derived-adjunction shift instance uses a different derived
adjunction construction and stronger ambient hypotheses; it cannot simply be
applied to this localization definition. Its proved cochain-unit instance does
apply, and the delivery supplies the localization glue explicitly.

Searches: msearch Loogle for `CategoryTheory.Adjunction.CommShift` returned the
generic class and constructors; msearch grep for localization/CommShift and
exactDerivedAdjunction returned generic localization and exact-functor APIs.
The saved msearch log also records successful LeanFinder searches for exact
derived-adjunction shift compatibility and localized-unit shift compatibility.
They returned the exact-functor shift/factorization instances and generic
derived-adjunction unit formulas. Direct rg inspection found and checked the
proved cochain-unit instance and the exact definition of the recorded adjunction.
No new node or separate unproved lemma was necessary.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
