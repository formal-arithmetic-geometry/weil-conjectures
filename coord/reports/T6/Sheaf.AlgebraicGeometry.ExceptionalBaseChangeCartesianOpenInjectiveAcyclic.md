## What changed

Proved the evaluation identity for higher direct image homology on affine weakly contractible objects and a sectionwise vanishing detection lemma. The target theorem now combines these with a new finite-stage hypercohomology model. Added `CartesianOpenFiniteStageHypercohomologyModel.lean` for the finite-principal-open exhaustion used by the target.

## Proved and sorry left

Closed one original hole, `AlgebraicGeometry.Scheme.isZero_higherDirectImage_cartesianOpen_injective`, by a complete Lean reduction. Added one strictly separate finite-stage-model hole. Net holes closed: zero; this is a decomposition, not a completed proof of the full acyclicity argument. The assigned module has zero remaining `sorry`s. The new declaration `AlgebraicGeometry.Scheme.exists_cartesianOpen_finiteStage_hypercohomology_model` remains `sorry`; node `lem-exc-cartesian-open-finite-stage-hypercohomology-model` records it.

## No longer needed

Removed direct proof imports (their geometric roles remain in the finite-stage model):

- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleVanishingDetection`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`

The separate node `lem-sf-proetale-vanishing-detection` is no longer needed: its role is discharged by the proved private sectionwise detection helper and `lem-weil-pbc-proetale-affine-wcontractible-covering-family`. No whole library module is claimed withdrawn.

The finite cohomological-dimension hypothesis is accepted by the target signature but is not needed by this reduction.

## Where the brief, the DAG or earlier work was wrong

The plan lacked a Lean declaration packaging the finite principal-open exhaustion and its colimit identification. This delivery records that genuinely separate construction as a new node. Intrinsic ringed-site modules cannot be passed directly to the fixed-coefficient detection theorem, so detection is proved sectionwise using sheaf separatedness and the existing affine weakly contractible covering family.

## New nodes

`lem-exc-cartesian-open-finite-stage-hypercohomology-model` records the finite-stage construction left as the remaining proof obligation.

The explicit resolution API from `lem-pe-bounded-complex-direct-image-presheaf` is used as a generic tool to compute the evaluation identity. Both delivered Lean modules compiled together without diagnostics (4.8 s and 10.1 s in the pruning check). The first completed dry run found a latent import cycle through `ProEtaleOpenInjectiveProperAcyclic`, `ProEtaleDerivedOpenRestriction`, and the parent `ProperExceptionalOpenBaseChange`. The new model module therefore does not import the unused quasi-compact acyclicity module. Its proof plan still names that declaration; proving the model will need to break this pre-existing dependency cycle before applying it.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
