## What changed

Restored `lean/Sheaf/Paper/ReconstructionUniformTower.lean` from its quarantined
interface, repairing `LocallyClosedStratification` to the current `Stratification`.
The module, its attachment and every reconstruction conclusion are retained.
The change record
`coord/changes/M4-reconstruction-stratification-restoration.md`
explains the identifier correction and consumer check.

The working source read at session start already contained eight auxiliary proofs;
these are retained. The adjacent ordinary reduction map is additionally proved.
Transpose the later quotient unit through the normalized tensor/restriction adjunction,
using cone naturality and the restriction-composition comparison. Scalar linearity
proves the formula on arbitrary pure tensors. Sheafification followed by tensor
induction proves uniqueness. The four new helpers are private and fully proved.

No adopted source-library file, target, definition data or public import is changed.
The existing DAG node records the actual auxiliary proof and its dependencies.
The complete module compiled through `lcompile.py` in 57.8 seconds.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.localReductionStep_exists`, one of the three holes
in the working source read at session start. No holes are added.

The eight retained proofs are `uniformTowers_grothendieck`,
`localReductionModuleTower_additive`, `localReductionDerived_exists`,
`uniformTowerLimit_additive`, `uniformConstantTower_additive`,
`uniformLocalProjections_naturality`, `uniformModuleTowerPull_preservesFiniteLimits`,
and `uniformModuleTowerPull_preservesFiniteColimits`, all in
`AlgebraicGeometry.Scheme`.

Relative to the current eleven-hole quarantine archive, nine holes are closed.
The actual remaining hole count is two, by declaration name:

- `AlgebraicGeometry.Scheme.localReductionEvaluation_exists`.
- `AlgebraicGeometry.Scheme.reconstructionUniformTower`.

Both retain their original statements, sources, complete natural-language proof plans
and the existing DAG node. The listed restoration/identifier repair is completed;
the reconstruction proof remains partial. There are no split-off assumptions.

The new adjacent-map proof uses only the cone equation, not surjectivity or any
nonzero coefficient-ring assumption. Its construction and uniqueness also apply to
zero coefficient rings and empty sites.

## No longer needed

Removed redundant direct proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.AdicCoefficientDatum`.
- `Sheaf.Paper.AdicLisseModule`.
- `Sheaf.Paper.CompletedAdicCoefficientDatum`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.FiniteReductionReconstructionCompleted`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Paper.KoszulReconstruction`.
- `Sheaf.Paper.TorsionLimitSheafCompleteness`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore`.

These are direct-import removals. No declaration or module is withdrawn and no
mathematical node is declared obsolete: the open geometric reconstruction theorem
still needs its recorded dependencies. Its seven proof steps and unit route remain.

## Where the brief, the DAG or earlier work was wrong

The current archive uses the unresolved identifier `LocallyClosedStratification`.
The already imported scheme stratification interface is `Stratification`.
The change record explains why the finite-type-over-a-field setting admits every
intended finite locally closed stratification, including constructibility of strata.

The shared checkout returned to the quarantine state while this session was running.
The packet preserves the entire module and its attachment, including the eight
auxiliary proofs from the initial working source. The report distinguishes that
initial three-hole source from the current eleven-hole archive.

An attempted proof of derived evaluation using resolving-subcategory descent still
exceeded the file-checking limit after several interface optimizations. It is not
claimed as proved: its original named obligation remains, and no intermediate
assumption is introduced. The completed adjacent-map proof and restoration are the
scope of this delivery.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
