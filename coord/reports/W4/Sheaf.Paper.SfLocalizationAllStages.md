## What changed

Decomposed `WeilConjectures.sfLocalizationAllStages` into finite/integral construction,
rational scalar transport, and algebraically closed common-stage descent. Its Lean proof
constructs a family over every finite coefficient field, extracts the finite-level witnesses
from the integral record, and assembles all four conjuncts. All original hypotheses and
conclusions are unchanged. The Weil theorem remains untouched.

Moved the 21 existing records, definitions, and proved inverse-limit formula to
`Sheaf.Paper.SfLocalizationData`, publicly re-exported by the original module. This is needed
so the construction lemmas can depend on the record types without importing their own consumer.
It was not a response to a timeout. All 23 existing signatures and all 21 moved bodies were
compared mechanically and match exactly. The prospective import graph is acyclic. All old public imports are retained in the data module.
No source-library module changes.

The three new modules use private proof imports for the relevant declared dependencies.
The construction theorems each have a source, a full proof in words and a DAG node.
Their empty-open, empty-closed and zero-object cases use the same recollement argument;
the cohomological-dimension bound is conditional only in the Tor fields. Rational and
common-stage construction are conditional on the earlier stages, so neither asserts the
original all-stage statement again under another name.

Validation: all five delivery modules compiled with `lcompile.py --all`. `Sheaf.Paper.FiniteClosedShriek` also compiled unchanged against the extracted
interface. `Sheaf.DeligneLaumon.QbarCurveDuality` timed out at 60 seconds both against the
extracted interface and against the original unmodified SfLocalizationAllStages module.
The identical baseline failure shows this is a pre-existing consumer compile issue; that
consumer is not edited or included in the delivery. The other direct consumer compiled
unchanged. No file was split to evade a timeout and no time limit was changed. The independent delivery reader performs
the mathematical review; no second reader was started.

## Proved and sorry left

Original holes: 2. Original holes closed syntactically: 1. New holes: 3.
This is a decomposition, not a net proof: net hole change is +2, and neither original
all-stage theorem is yet proved without `sorryAx` in its dependencies.

- `WeilConjectures.sfLocalizationAllStages` has a complete combining proof; its former
  hole is reduced to the following three strictly smaller coefficient-passage steps.
- `WeilConjectures.sfIntegralLocalizationConstruction` remains `:= by sorry`, node
  `lem-sf-integral-localization-construction`: only finite/integral operations and reductions.
- `WeilConjectures.sfRationalLocalizationConstruction` remains `:= by sorry`, node
  `lem-sf-rational-localization-construction`: rational transport given an integral record.
- `WeilConjectures.sfCommonStageLocalizationConstruction` remains `:= by sorry`, node
  `lem-sf-common-stage-localization-construction`: common-stage descent given rational records.
- `WeilConjectures.sfLocalizationAllStages_weil` retains its original `:= by sorry`, node
  `prop-sf-localization-all-stages`.

The existing proved `WeilConjectures.sfLocalizationExceptionalLimit` is preserved verbatim;
no new hole is introduced in any data, definition or instance. SfLocalizationData has zero holes.

## No longer needed

No module is withdrawn and no upstream declaration is removed. None of the original public
imports is dropped from the public import closure: each is retained in SfLocalizationData.
The main theorem now imports only the three construction modules for its proof.
The old direct proof dependencies are distributed to those new nodes, rather than discarded:
finite kernel localization, integral ordinary realization, exceptional reductions and site
normalization, immersion intervals, open uniform and residue bounds, Tor propagation,
rational transport, scalar extension, and common-stage descent remain needed there.
The separate closed-unit all-stage theorem is not needed for assembling the records here:
closed full faithfulness and the adjunction in the kernel/ordinary realization give the
unit clauses. The separate finite-type Noetherian and dimension-bound leaves are no longer
direct dependencies of this combining proof; their geometric facts remain in the construction
arguments. The Weil mate-lift and Weil-operation nodes remain attached to the untouched Weil hole.
No global module-pruning count is claimed.

The following original private proof imports are removed from the original module and are
not included as private imports in the data module. Some remain transitively needed through
the declared construction dependencies; this is removal of unused direct imports, not a claim
that their mathematics is globally obsolete:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.SfIntegralDirectImageConstructible`
- `Sheaf.Paper.SfIntegralConstructible`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.CompletedPullbackReduction`
- `Sheaf.Paper.PerfectProjectionFormula`
- `Sheaf.Paper.ProjectionMateExact`
- `WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `Sheaf.AlgebraicGeometry.DerivedOpenImmersionFullyFaithful`
- `Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions`
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.CategoryTheory.Shift.Adjunction`
- `Mathlib.CategoryTheory.Triangulated.Adjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.Paper.PbcRationalTransport`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.PbcScalarExtension`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.PbcDescentFunctors`
- `Sheaf.Paper.PbcVerdierAxioms`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.ProEtaleResidueTorTest`
- `Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`
- `Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension`
- `Mathlib.AlgebraicGeometry.Properties`
- `WeilConjectures.RingTheory.Etale.LocalDimension`
- `Sheaf.AlgebraicGeometry.QcqsHigherDirectImage`
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula`
- `Sheaf.Paper.FiniteCtfTriangulated`
- `Mathlib.CategoryTheory.Triangulated.Subcategory`
- `Sheaf.Paper.IntegralCtfTriangulated`
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`

## Where the brief, the DAG or earlier work was wrong

The planned declaration applications need additional bridge work. In particular,
`FiniteExceptionalNormalization.finiteExceptionalSiteNormalization` assumes a finite-field
datum, whereas the assigned theorem allows an arbitrary field. Its argument must be generalized
using torsion site comparison before it can normalize the specified finite exceptional functor
here. `AlgebraicGeometry.ProEtale.immersion_residue_tor_intervals` takes its coefficient field
in `Type (u + 1)` while this module uses `E : Type u`; an intrinsic realization/universe bridge
is required. The new finite/integral construction statement records exactly where these steps
remain, and its docstring does not pretend either declaration applies directly.

The existing all-stage record types must be available to construction lemmas without making
an import cycle. The new data module supplies that interface; it does not alter any definition.
No statement was found false, no target changes, and no unit route is bypassed. The ordinary
open/closed Hom construction still belongs to the finite-kernel and ordinary-recollement inputs.
The current blueprint text was read at `literature/blueprint/latest/`.
A dependency traversal found a pre-existing two-node cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`, outside this delivery. No cycle
involving the delivery nodes was found. This unrelated graph defect is reported here
for the maintainer; its nodes were not edited.

## New nodes

`def-sf-localization-stage-data` attaches the unchanged 21 moved declarations to their new
module. It introduces no new mathematical construction or hole.

`lem-sf-integral-localization-construction` isolates the finite/integral assembly, including
actual exceptional normalization, normalized reductions and conditional uniform Tor bounds.

`lem-sf-rational-localization-construction` isolates scalar transport from an integral record;
it needs no algebraically closed stage.

`lem-sf-common-stage-localization-construction` isolates descent from a family of rational
records to the algebraically closed category. The main proof supplies that family at every field.

Change record: `coord/changes/W4-sf-localization-stage-data.md`. It lists all 116 transitive
consumers, current holders where available, and explains the unchanged public interface.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
