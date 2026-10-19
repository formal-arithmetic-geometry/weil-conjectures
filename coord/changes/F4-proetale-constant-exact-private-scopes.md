# finiteCoefficientModulePullback_exact

## Reason

The delivery proves four existing theorems without changing their statements or any
existing definition. Preflight nevertheless classifies added section/open commands and
proof elaboration options around private helpers as an interface change. This record
makes that classification reviewable. The helpers transport the actual RingCat inverse
image adjunction to the small site model and identify module inverse image on underlying
abelian sheaves. Their opens and options are confined to sections which end before the
existing declarations resume. An additional theorem-local unused-section-variable linter
option retains the original finite/discrete hypotheses on the commutative map theorem.
All public imports, existing attributes, declaration signatures, and data definitions
are unchanged. Target meanings and types are unchanged. There are no forced adaptations.

## Old

The public theorem signatures, verbatim (proofs were sorry):

```lean
theorem finiteCoefficientModulePullback_additive :
    (finiteCoefficientModulePullback f Λ).Additive

theorem finiteCoefficientModulePullback_exact :
    PreservesFiniteLimits (finiteCoefficientModulePullback f Λ) ∧
    PreservesFiniteColimits (finiteCoefficientModulePullback f Λ) ∧
    ∀ S : ShortComplex (FiniteCoefficientModules V Λ),
      S.ShortExact → (S.map (finiteCoefficientModulePullback f Λ)).ShortExact

theorem finiteCoefficientCommRing_preservesSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

theorem finiteCoefficientCommRingMap_isIso :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ))
```

The namespace following the original top-level open commands began immediately:

```lean
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale
```

## New

The same public theorem signatures, verbatim (proofs now supplied):

```lean
theorem finiteCoefficientModulePullback_additive :
    (finiteCoefficientModulePullback f Λ).Additive

theorem finiteCoefficientModulePullback_exact :
    PreservesFiniteLimits (finiteCoefficientModulePullback f Λ) ∧
    PreservesFiniteColimits (finiteCoefficientModulePullback f Λ) ∧
    ∀ S : ShortComplex (FiniteCoefficientModules V Λ),
      S.ShortExact → (S.map (finiteCoefficientModulePullback f Λ)).ShortExact

theorem finiteCoefficientCommRing_preservesSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

theorem finiteCoefficientCommRingMap_isIso :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ))
```

Before that namespace, a new section holds private RingCat comparison helpers, with
these exact command lines; its final end closes the section:

```lean
section
open Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Within ProEtale a second section holds private abelian comparison helpers:

```lean
section
open Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
open Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

It ends before finiteCoefficientModulePullback_exact. Both sections contain proved
private declarations only. The existing commutative map theorem additionally has the
scoped command `set_option linter.unusedSectionVars false in`; its proof uses scoped
backward elaboration options. None changes what an importer can name or infer.

## Users

No module is adapted. Direct importers were checked by source search and the required
read-only downstream command was run. Since every original public signature, data
construction, attribute and public import is identical, all direct and transitive
consumers retain the same interface. The group column records that no consumer's work
is touched; ownership is immaterial in the absence of any adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleConstantExact | F4 | Four proofs supplied; private helpers and scoped commands added. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedSupportAdjunction | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenDerivedImage | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtalePairFlasque | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | not adapted | Public interface unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.SupportLocalizationTriangle | not adapted | Public interface unchanged; no edit required. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.ClosedSupportedCupVanishing | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.CompactSupportPerfectness | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.CompletedExtensionZeroComparison | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.CompletedOpenExchangeTransport | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.CompletedPullbackTensorComparison | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.ConcentratedComplexShift | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.ConstructiblePullbackTExact | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.DerivedPullbackTensorIso | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.ExplicitExceptionalPreservation | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.FinitePullbackTensorComparison | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.IntegralCoherenceTower | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.IntegralDerivedOperations | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.IntegralOperationsScalarExtension | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.IntegralOperationsWellDefined | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.IntegralPullbackComposition | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.PullbackTorAmplitude | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.PurityFiniteKummerLevel | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.PurityGeneralAdmissibility | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.StratumScalarExtension | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.SupportedHomPullback | not adapted | Public interface unchanged; no edit required. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | Public interface unchanged; no edit required. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not adapted | Public interface unchanged; no edit required. |
| Sheaf.SixFunctors.OpenTensorNormalization | not adapted | Public interface unchanged; no edit required. |
| Sheaf.SixFunctors.SchemeGaloisComparison | not adapted | Public interface unchanged; no edit required. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not adapted | Public interface unchanged; no edit required. |
| Sheaf.TraceFormula.PointTransportComposition | not adapted | Public interface unchanged; no edit required. |

## Status

landed 20261019T002544-L-2152465 2026-10-19 (merge of deliver/F4/Sheaf.AlgebraicGeometry.ProEtaleConstantExact)
