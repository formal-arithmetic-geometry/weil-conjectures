## What changed

Proved `DerivedCategory.exists_boundedAbove_projective_model` in
`Sheaf.Algebra.Homology.BoundedAboveProjectiveModel`, with its signature and public imports
unchanged. The proof uses the standard t-structure to choose a representative strictly zero
above the specified bound, applies Mathlib's exact-bound injective replacement in the opposite
category with degrees reversed, and transports the resulting projective model back through
localization. A proved private helper `quasiIso_unop_reverse` checks the quasi-isomorphism
transfer on three-term short complexes.

Added proof-only imports of `Mathlib.Algebra.Category.ModuleCat.Projective`,
`Mathlib.Algebra.Homology.CochainComplexOpposite`, and
`Mathlib.Algebra.Homology.Factorizations.CM5a`. Updated the item's DAG proof and proof dependencies
to describe this dual argument. The source itself states the projective-resolution result as
the dual of injective resolutions. No definitions, existing interfaces, or consumers changed.

## Proved and sorry left

Closed the one original hole in `DerivedCategory.exists_boundedAbove_projective_model`
(node `lem-weil-pbc-bounded-above-projective-model`). Added zero holes, and left zero holes.
The private helper is also proved. This is a proof, with no decomposition or split-offs.

The module compiles cleanly through `lcompile.py`. The delivery axiom probe passed for every declaration in the module, allowing only
`propext`, `Classical.choice`, and `Quot.sound`. The proof is entirely from Mathlib; no unproved Sheaf declarations
are used.

The arbitrary integer bound, including negative bounds, is retained exactly by n ↦ -n.
The zero object and zero ring require no exceptional cases. Module universes stay at
`max u v`, and the derived-category morphism universe `w` is unchanged.

## No longer needed

Removed the direct proof-only import `Mathlib.LinearAlgebra.FreeModule.Basic`. The explicit
free-on-compatible-pairs descending recursion, and its separate cycle/boundary lifting proofs,
are unnecessary: the opposite of Mathlib's existing injective replacement supplies the model.
No Sheaf module or DAG node is pruned. In particular, `def-weil-pbc-free-module` and
`lem-weil-pbc-free-module-projective` still explain the free presentations in the standard
`ModuleCat.enoughProjectives` instance; they are retained in the DAG proof dependencies.
The unit's statement and realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier searches had already found the injective dual but treated dualization as a separate
construction. `CochainComplex.opEquivalence` supplies that construction, and
`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective` supplies the precise bound.
Only the short-complex quasi-isomorphism check had to be proved here.

The existing Mathlib leaf `lem-sc-bounded-below-injective-resolution-existence` names the bundled
version of this replacement. This proof uses its underlying unbundled theorem in CM5a, whose
signature explicitly preserves the lower bound; it does not infer that stronger bound merely
from the leaf's natural-language existential statement. No false statement or definition repair
was necessary, and no new nodes were introduced.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
