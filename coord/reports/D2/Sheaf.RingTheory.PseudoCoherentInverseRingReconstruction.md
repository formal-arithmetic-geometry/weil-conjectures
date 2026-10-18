## What changed

Added the proof-only module `Sheaf.RingTheory.PseudoCoherentInverseRingReconstructionModels` with the strictly smaller `DerivedCategory.reconstruction_models` intermediate theorem. The item theorem applies that model statement, derives pseudo-coherence from its bounded finite-free limit model, proves each projection transpose is an isomorphism from the final compatibility equation, and repackages every model clause unchanged.

## Proved and sorry left

The original declaration `DerivedCategory.isPseudoCoherent_inverse_ring_reconstruction` is proved. The intermediate declaration `DerivedCategory.reconstruction_models` remains `sorry`; it is recorded by node `lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction-models`.

## No longer needed

The item module no longer imports these proof-only modules directly:

- `Sheaf.Algebra.Homology.BoundedFlatKFlat`
- `Sheaf.RingTheory.PseudoCoherentNilpotentInvariance`
- `Mathlib.Algebra.Homology.DerivedCategory.KProjective`
- `Mathlib.RingTheory.TensorProduct.Basic`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Mathlib.CategoryTheory.Triangulated.Triangulated`
- `Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit`
- `Sheaf.RingTheory.NilpotentMarkedFreeComplexLift`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`

Those imports remain in the proof-only models module where the split theorem is stated.

## Where the brief, the DAG or earlier work was wrong

The original theorem combines the finite-free tower construction with its pseudo-coherence and projection consequences. The tower construction is a distinct strictly smaller statement and must be proved separately before the upper theorem can be closed.

## New nodes

Created `lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction-models`, recording the compatible finite-free model existential clause and its source in Stacks Tag 0CQF. Its declaration is in `lean/Sheaf/RingTheory/PseudoCoherentInverseRingReconstructionModels.lean`.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
