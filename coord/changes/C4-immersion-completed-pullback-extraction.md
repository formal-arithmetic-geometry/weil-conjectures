# AlgebraicGeometry.Scheme.ImmersionCompletedPullback coefficient API

## Reason

Repair of return C-ddea0 (ddea060962c), points 2b/A3 and D1. The unnecessary
CoreB extraction is undone: strictIso_exists through roosRlim, including private
helpers, remain verbatim in the item with the original section setup and
strictIso_exists docstring. Its duplicate models node is removed, and its 21
public names return to the item node's declaration list. No existing
mathematical definition or statement changes.

Only the CoreA extraction remains: the finite-level split must import the
coefficient and finite normalization API independently of the theorem that
consumes it. The item publicly reexports that API and uses import all CoreA.
The existing definition ownership node is not changed.

## Old

Current main declares the following 21 public coefficient/finite signatures in
the item, under the original ambient l, E, X, Y and f variables:

```lean
theorem quotientEquiv_exists (n : ℕ) : ∃! e : PbcQuotient (pbcIntegralDatum l E) n ≃+* ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)), ∀ a : PbcIntegralRing l E, e (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)) a) = ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down)

def quotientEquiv (n : ℕ)

def finiteRingIso (T : Scheme.{u}) (n : ℕ) : (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅ integralCoefficientCommRingSheaf l E T n

theorem completedRingIso_exists (T : Scheme.{u}) : ∃! e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅ completedIntegralCommRingSheafUnrestricted l E T, ∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n = pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (finiteRingIso l E T n).hom

def completedRingIso (T : Scheme.{u})

abbrev transport (T : Scheme.{u}) : PbcCompletedDerived T (pbcIntegralDatum l E) ⥤ DerivedCategory (scalarReductionSource.{u, u} l E T)

theorem moduleObj_eq (M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) : (pbcActualModulePull f (pbcIntegralDatum l E)).obj M = (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)).obj M

theorem moduleObj_eq_naturality {M N : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))} (a : M ⟶ N) : (pbcActualModulePull f (pbcIntegralDatum l E)).map a ≫ eqToHom (moduleObj_eq l E f N) = eqToHom (moduleObj_eq l E f M) ≫ (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)).map a

def moduleIso : pbcActualModulePull f (pbcIntegralDatum l E) ≅ proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)

theorem derivedIso_exists : ∃! e : pbcActualDerivedPull f (pbcIntegralDatum l E) ≅ (pbcIntegralDatum.{u} l E).pull.{u} f, whiskerLeft DerivedCategory.Qh e.hom ≫ (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)).mapDerivedCategoryFactorsh.hom = pbcActualPullCounit f (pbcIntegralDatum l E) ≫ whiskerRight (NatTrans.mapHomotopyCategory (moduleIso l E f).hom (.up ℤ)) DerivedCategory.Qh

def derivedIso

def finiteComparison (n : ℕ) : (pbcIntegralDatum l E).reduction X n ⋙ (pbcIntegralDatum l E).finitePull f n ≅ pbcActualDerivedPull f (pbcIntegralDatum l E) ⋙ (pbcIntegralDatum l E).reduction Y n

abbrev restrictedReduction (T : Scheme.{u}) (n : ℕ)

def reductionUnit (T : Scheme.{u}) (n : ℕ)

def reductionTransition (T : Scheme.{u}) (b a : ℕ) (h : a ≤ b) (K : PbcCompletedDerived T (pbcIntegralDatum l E)) : (restrictedReduction l E T b).obj K ⟶ (restrictedReduction l E T a).obj K

def restrictedComparison (n : ℕ) : restrictedReduction l E X n ⋙ (pbcIntegralDatum l E).pull f ≅ (pbcIntegralDatum l E).pull f ⋙ restrictedReduction l E Y n

theorem finite_compatibility : (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ), ((pbcIntegralDatum l E).pull f).map ((reductionUnit l E X n).app K) ≫ (restrictedComparison l E f n).hom.app K = (reductionUnit l E Y n).app (((pbcIntegralDatum l E).pull f).obj K)) ∧ (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (b a : ℕ) (h : a ≤ b), ((pbcIntegralDatum l E).pull f).map (reductionTransition l E X b a h K) ≫ (restrictedComparison l E f a).hom.app K = (restrictedComparison l E f b).hom.app K ≫ reductionTransition l E Y b a h (((pbcIntegralDatum l E).pull f).obj K)) ∧ (∀ (T : Scheme.{u}) (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c), reductionTransition l E T c b hbc K ≫ reductionTransition l E T b a hab K = reductionTransition l E T c a (hab.trans hbc) K)

theorem moduleTowerEvaluation_eq (n : ℕ) : (pbcIntegralDatum l E).towerModulePull f ⋙ reductionTowerEvaluation Y (reductionModuleRing Y ((pbcIntegralDatum l E).completedRing Y)) n = reductionTowerEvaluation X (reductionModuleRing X ((pbcIntegralDatum l E).completedRing X)) n ⋙ proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)

def towerEvaluationIso (n : ℕ)

def completedProjection (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) : ((pbcIntegralDatum l E).completedPull f).obj K ⟶ ((pbcIntegralDatum l E).pull f).obj ((restrictedReduction l E X n).obj K)

theorem completedProjection_compatibility : (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ), (pbcIntegralDatum l E).ordinaryToCompleted f K ≫ completedProjection l E f K n = ((pbcIntegralDatum l E).pull f).map ((reductionUnit l E X n).app K)) ∧ (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (b a : ℕ) (h : a ≤ b), completedProjection l E f K b ≫ ((pbcIntegralDatum l E).pull f).map (reductionTransition l E X b a h K) = completedProjection l E f K a)
```

Its public imports are:

```lean
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
```

## New

The signatures above and every existing definition body remain identical in
SfImmersionCompletedPullbackCoreA. The item retains the same public imports and
adds:

```lean
public import Sheaf.Paper.SfImmersionCompletedPullbackCoreA
import all Sheaf.Paper.SfImmersionCompletedPullbackCoreA
```

All 21 strict/Roos public declarations from the returned CoreB remain in the
item, with their original signatures and bodies verbatim. Only the final
comparison theorem's proof changes from current main. No target meaning
changes. The item node's stmt_deps stays unchanged and proof_deps is the union
of actual uses; no duplicate models ownership node remains in the packet.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralPullbackStrictRoosData | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.IntegralImmersionPullbackNormalizationData | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.CompletedPullbackUniverseTransportData | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.CompletedOpenTensorSystemRealization | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.IntegralPullbackCompletedComparisonData | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.SfIntegralOrdinaryRecollementRealization | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.FinitePullbackStrictTowerComparison | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.IntegralPullbackShiftCoordinates | unclaimed | Direct importer; unchanged source compiled against CoreA reexport and restored item. |
| Sheaf.Paper.CompletedIntegralFiniteTowerTransport | unclaimed | Transitive textual use; public names and signatures remain identical. |
| Sheaf.Paper.FdPullbackSignedShiftWordTransport | unclaimed | Transitive textual use; public names and signatures remain identical. |
| Sheaf.Paper.IntegralImmersionPullbackNormalization | unclaimed | Transitive textual use; public names and signatures remain identical. |
| Sheaf.Paper.IntegralImmersionShiftCompatibility | unclaimed | Transitive textual use; public names and signatures remain identical. |
| Sheaf.Paper.IntegralRoosDerivedPullbackUnit | unclaimed | Transitive textual use; public names and signatures remain identical. |
| Sheaf.Paper.IntegralStratumChartRestrictions | unclaimed | Transitive textual use; public names and signatures remain identical. |
| Sheaf.Paper.IntegralStratumChartRestrictionsData | unclaimed | Transitive textual use; public names and signatures remain identical. |
| Sheaf.Paper.IntegralStratumChartRestrictionsFunctorial | unclaimed | Transitive textual use; public names and signatures remain identical. |

All direct importers in the current snapshot are listed first. Unchanged copies
are temporary compilation inputs and are removed before delivery. All ten direct importers passed (7.7 to 30.6 seconds); no forced adaptation
was necessary. Other rows are the textual transitive users of the
extracted names; unchanged reexported signatures preserve their interfaces.

## Status

landed 20261027T180511-L-3867707 2026-10-27 (merge of deliver/C4/Sheaf.Paper.SfImmersionCompletedPullbackComparison)
