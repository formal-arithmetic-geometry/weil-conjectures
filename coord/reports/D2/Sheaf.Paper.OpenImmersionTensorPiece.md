## What changed

Updated `Sheaf.Paper.OpenImmersionTensorPiece` by adding the named intermediate theorem
`SheafOfModules.openImmersionTensor_exists`, which states existence of the normalized
natural isomorphism. The main theorem `SheafOfModules.openImmersionTensor_iso` now
obtains that isomorphism and proves its uniqueness formally from injectivity of the
localized module adjunction hom-equivalence. The theorem statement and all existing
definitions remain unchanged. The copied node updates the proof route to record the
existence split and the formal uniqueness step.

## Proved and sorry left

Closed the original hole of `SheafOfModules.openImmersionTensor_iso` by reducing it to
the strict existence statement and proving uniqueness in Lean. One sorry remains in
`SheafOfModules.openImmersionTensor_exists`; it is recorded by node
`lemma-weil-pbc-projection-formula-open-piece-existence` and contains the finite-free
retract, signed totalization, K-flat resolution, and derived descent construction.

## No longer needed

Removed the proof-only imports that were not needed by the formal existence reduction:
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`Sheaf.CategoryTheory.ModulePullbackTensorIso`,
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescent`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
`Mathlib.Algebra.Homology.BifunctorShift`, `Sheaf.Algebra.Homology.KFlat`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, and
`Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`. The detailed proof-plan nodes
remain dependencies of the split existence node; no other nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The original module's theorem proof was only `sorry`, while its docstring contained a
five-step construction. The DAG treated the entire construction and the normalization
uniqueness as one proof obligation. The delivery separates the non-formal existence
construction from the formal uniqueness argument without changing the target statement.

## New nodes

`lemma-weil-pbc-projection-formula-open-piece-existence` records the strict existence
part of the imported proof and is attached to
`SheafOfModules.openImmersionTensor_exists` in the existing module. Its proof plan
contains the finite-free comparison, degreewise strict-perfect retract transport,
signed totalization, K-flat resolution, and derived tensor descent steps.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
