# AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit imports

## Reason

The theorem now has a complete proof from its recorded dependencies. The two withdrawn
packages contain no declarations. LimitAffineTransition, SiteSystemStrictification,
ColimitSites, and the cohomology API FullAffineEtaleTopos are not used directly. Replace
their public imports with the statement APIs: FullAffineEtaleSite, continuous functors,
finite precoverages, and the arrows functor. Remove the empty proof import of
AffineEtaleColimitPresentation. Keep the finite presentation theorem as a proof-only
import. No declaration signature, visibility, definition, instance or target changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
public import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Sheaf.CategoryTheory.SiteSystemStrictification
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Sheaf.CategoryTheory.ColimitSites
import Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeSystem
import Sheaf.AlgebraicGeometry.AffineEtaleDescentData
import Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentationFinite
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Sheaf.CategoryTheory.ArrowsFunctor
import Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeSystem
import Sheaf.AlgebraicGeometry.AffineEtaleDescentData
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentationFinite
```

## Users

The complete transitive inventory is from tools/downstream.py and the source imports.
The sole direct importer, AffineComparisonInjectiveVanishing (holder V3), imports this
module privately. Its unchanged source compiles against this delivery's sandbox output,
with explicit import-artifact overrides supplied by lcompile.py. It separately imports
LimitAffineTransition and the other APIs it mentions. No consumer is edited. Its private
import prevents these public-import removals from affecting public interfaces farther
upstream. All declaration statements are identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing | V3 | Direct proof importer; compiles unchanged against the pruned interface. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | T4 | Indirect importer; direct edge is private, so its public interface is unaffected. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | C2 | Indirect importer; direct edge is private, so its public interface is unaffected. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| TargetsCheck | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Comparison | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Counterexample | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | V2 | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.AlgClosedField | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Comparison | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonMonoidal | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Constructible | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.FlatModel | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Shift | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitudeResidue | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Derived.WeilComplex | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.Statement | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Indirect importer; direct edge is private, so its public interface is unaffected. |

## Status

landed 20261015T213648-L-2155128 2026-10-15 (merge of deliver/W3/Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement)
