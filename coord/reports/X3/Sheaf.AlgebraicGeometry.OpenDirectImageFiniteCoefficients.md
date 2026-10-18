## What changed

Closed the sole hole in
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`
without changing its signature, universes, hypotheses, visibility, definitions or public imports.
The proof uses the existing source-library arbitrary-finite-coefficient open-image sheaf
corollary, the proved finite-truncation devissage lemma, and the proved comparison of
finite-value and finite-stalk constructibility. The support interval is converted explicitly
to standard t-structure bounds and back. Only the assigned Lean module and its DAG proof
record change; no new Lean module, node, or statement is introduced.

Validation: the remote single-file compiler accepted the proof. An import-removal check
confirmed that the Triangulated import is necessary: without it the generic right-derived
functor has no synthesizable IsTriangulated instance. All new imports are proof-only.

The standard finite-truncation argument is an explicitly permitted alternative to the
spectral sequence in the source proof. The unit sk-prop-sf-cbc has empty realized.statement
and realized.steps lists, so this changes no unit-level realization.

## Proved and sorry left

Holes closed (1):
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`
(node `cor-fin-deligne-open-finite-coefficients`).
Holes added: 0. Holes left in the delivered module: 0. Split off: 0.

This is a complete relative proof, not an axiom-free completion of Deligne finiteness.
The existing source corollary
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field`
has a complete Lean proof, but depends on the existing
`AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn` sorry in
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne`.
The source implements generic Deligne finiteness for arbitrary finite coefficients;
the DAG's separately recorded Sheaf corollary is only its prime-field specialization.
No claim of eliminating that existing underlying obligation is made.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.AlgebraicGeometry.OpenDirectImageOverField`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`

The following former proof dependencies and their top-level tool-use approvals are removed:

- `lem-weil-pbc-module-abelian-derived-direct-image-comparison`: arbitrary finite
  coefficients are already admitted by the source open-image sheaf corollary.
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-derived-functor-long-exact`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-dplus-injective-representative`
- `thm-sp-truncation-e2`

The latter six are unnecessary because the proved finite-truncation lemma already supplies
passage to bounded complexes. `def-weil-pbc-constructible-complexes` remains a statement
dependency but need not additionally be a proof dependency. Constructible Serre closure
remains used inside finite truncation devissage. The prime-field Sheaf wrapper is not
imported; the source corollary realizing the same mathematical open-image finiteness input
is used in its existing arbitrary-finite-coefficient generality. These are removals from
this proof route, not a claim that no other target needs those modules.

## Where the brief, the DAG or earlier work was wrong

The planned six-step coefficient devissage is unnecessary given the current source
library: Deligne.lean already supplies the open-image sheaf result for arbitrary finite
allowable commutative coefficients, and BoundedConstructible.lean already proves the
extension to bounded complexes. The original blueprint itself explicitly permits finite
truncation triangles in place of the truncation spectral sequence. No mathematical
statement is disputed or changed. The dependency on the pre-existing, more general generic
Deligne theorem is recorded explicitly above and in the updated proof record.

Searches: LeanFinder returned only Mathlib scheme/open-immersion facts, not etale finiteness;
Loogle rejected the attempted quoted induction query; msearch grep found no Mathlib
match. Direct rg of the project's source library found Deligne.lean and the finite
truncation lemma. No external result or newly assumed lemma is introduced.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
