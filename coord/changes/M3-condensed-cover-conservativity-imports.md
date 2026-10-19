# AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative

## Reason
The completed proof reuses the published generic pro-etale restriction criterion.
The former public imports of constant-ring operations and slice comparisons are
unnecessary for either its statement or proof. Removing them avoids those proof
branches. No definition, statement, universe, visibility or coefficient map changes.
The `ZeroObject` scope is opened solely to write the proof's map from K to zero.

## Old
```lean
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
```

## New
```lean
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
```
The theorem's signature is identical. The new private helper is proved and is used
only by this proof; it occurs in no public signature or definition.

## Users
Both direct importing modules were compiled unchanged against the replacement
module in a separate sandbox check: CondensedLisseProEtaleLocality in 5.1 seconds
and MateOpenRestriction in 11.6 seconds. No importer needs an adaptation. Every
transitive source importer is listed below for the independent reader.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | M3 | Assigned proof completed; unused public imports removed; signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | Direct importer; original file compiles against the pruned interface without edits. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 | Direct importer; original file compiles against the pruned interface without edits. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| TargetsCheck | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Indirect importer; signatures and meaning unchanged; no adaptation. |

| WeilConjectures | unclaimed | Indirect root importer; signatures and meaning unchanged; no adaptation. |

## Status
landed 20261019T112455-L-3943584 2026-10-19 (merge of deliver/M3/Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative)
