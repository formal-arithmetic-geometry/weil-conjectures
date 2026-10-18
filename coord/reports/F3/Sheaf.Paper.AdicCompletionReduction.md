## What changed

Proved `AlgebraicGeometry.Scheme.adicDerivedRestrict_reflectsIsomorphisms` in
`lean/Sheaf/Paper/AdicCompletionReduction.lean`. The proof installs the standard derived
category instances, establishes conservativity of scalar restriction through the underlying
sheaf functor, and applies the derived isomorphism criterion degree by degree on homology.
Added the proof-only import `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` for the exact-functor homology comparison.

## Proved and sorry left

Closed one existing sorry: `adicDerivedRestrict_reflectsIsomorphisms` (node
`lem-weil-pbc-adic-derived-restrict-conservative`). Two existing named sorries remain:
`adicReductionAdjunction_homEquiv_exists` (node
`lem-weil-pbc-adic-reduction-adjunction-hom-equiv`) and
`adicCompletionReduction_restricted_isIso` (node
`lem-weil-pbc-adic-completion-reduction-restricted`). No new sorries were added.

## No longer needed

None. The proof uses the existing scalar restriction, sheafification, and derived-category
imports and does not prune any declared dependency.

## Where the brief, the DAG or earlier work was wrong

Nothing identified. The conservativity proof follows the stated proof step and preserves the
existing declaration signature.

## New nodes

None.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
