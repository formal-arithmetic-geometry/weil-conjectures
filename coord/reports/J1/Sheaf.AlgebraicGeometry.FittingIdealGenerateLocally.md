## What changed

Proved `AlgebraicGeometry.Scheme.Modules.fitting_ideal_generate_locally` without changing its
statement, definitions, or existing public imports. The affine formula comes from
`fittingIdealSheaf_affine_sections`. For the stalk criterion, localize the finite section
module using `isLocalizedModule_affine_germ` and use presentation independence and arbitrary
base change. Over the local ring, specialize
`LinearMap.exists_fin_generators_quotient_fittingTorsion` to `f = 1`; its quotient is the
original module. The reverse implication computes the ideal of a presentation with exactly
`r` generators. The existing ideal zero-set dictionary gives the ideal-stalk equivalence.

Added `Sheaf.AlgebraicGeometry.FiniteStalkGeneratorsNeighborhood`, proving that a finite type
module sheaf has at most `r` generators near a point exactly when its actual stalk does.
This independent sheaf lemma requires neither quasi-coherence nor finite presentation. Its
proof represents finitely many germs and coefficient germs on common neighbourhoods,
shrinks finitely many equations, and applies local lifting for epimorphisms. It includes
`r = 0` and uses no choice of data from unproved existence statements.

For an arbitrary pullback, `fittingSheaf_arbitrary_pullback` supplies finite type,
quasi-coherence, and ideal pullback. Mathlib's `IdealSheafData.support_comap` and
`IsOpenImmersion.lift` then prove the factorization criterion. The DAG now records this route. The added proof imports provide affine germ localization,
the ideal zero-set dictionary, quotient and tensor finiteness APIs, finite linear
combinations, and open-immersion lifting; they are private imports.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.fitting_ideal_generate_locally`
(node `lem-trf-fitting-ideal-generate-locally`): 1 of 1 original holes.

Added no holes. The new
`AlgebraicGeometry.Scheme.Modules.finite_stalk_generators_iff_neighbourhood`
(node `lem-trf-finite-stalk-generators-neighbourhood`) and all private helpers have complete
proofs. No `sorry` remains in either delivered Lean module. The proof uses existing stated
dependencies, including the still-unproved presentation, principal-Fitting, affine-section,
and arbitrary-pullback theorems; this does not claim that their transitive axioms are closed.

Validation: `lcompile.py --all` compiled both delivered modules without errors or
warnings: 26.9 seconds for `FiniteStalkGeneratorsNeighborhood`, 15.3 seconds for
`FittingIdealGenerateLocally`. Both are below the 60-second per-file limit.
Temporary algebra and assembly check modules were removed before this final compile.

## No longer needed

Removed the private proof imports `Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Mathlib.LinearAlgebra.Matrix.Adjugate`, and
`WeilConjectures.AlgebraicGeometry.TensorPullbackTilde` from the item module.

The parent proof no longer directly needs `lem-trf-invertible-relation-minor-generators`
(`Sheaf.RingTheory.InvertibleRelationMinorGenerators`) or
`lem-weil-pbc-affine-tilde-gamma-adjunction` (`Mathlib.AlgebraicGeometry.Modules.Tilde`).
The local-ring specialization replaces the explicit invertible-minor construction, and
`isLocalizedModule_affine_germ` directly supplies the tensor/stalk comparison.
`def-weil-pbc-generating-sections` is used in the new general sheaf lemma rather than as a
direct proof dependency of the parent. The invertible-minor node has no other current DAG parent and its module has no Lean
importer; this route removes its remaining planned use. No module or declaration is
withdrawn. The other nodes remain available to their users.

Removed the obsolete top-level approval for `lem-weil-pbc-tilde-pullback-base-change`:
its use is encapsulated by `lem-trf-fitting-sheaf-arbitrary-pullback`, whose dependencies
remain unchanged. The parent no longer directly uses the old docstring's separate
`lem-weil-pbc-matrix-adjugate-identity` or `lem-weil-pbc-spec-module-tilde-sections` steps.
These ingredients may still occur in the existing black-box dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was corrected. Updated the declaration docstring and DAG proof steps from the older constructive minor
route to the shorter actual Lean proof.
The original DAG omitted the already-stated affine-sections theorem as a direct dependency,
although that theorem gives the first conjunct immediately.

The new node uses the existing generic local-coefficient and local-epimorphism germ-lift
lemmas from the proper-base-change chapter as sheaf tools. Both declarations already have
complete proofs; no step of the trace-formula unit is bypassed. The new general criterion
is not another Fitting-locus assertion and contains no Fitting ideal or pullback.

## New nodes

`lem-trf-finite-stalk-generators-neighbourhood` is the finite-type sheaf criterion just
proved in `Sheaf.AlgebraicGeometry.FiniteStalkGeneratorsNeighborhood`. Its source is
Stacks Project, Modules, Tag 01B8, with the finite representation/equality argument
expanded. The statement has been checked for zero generators, zero stalks, and empty
schemes. Mathlib searches and the blueprint duplicate searches found no matching statement.
No change record is needed: existing public signatures, definitions, and imports are unchanged.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
