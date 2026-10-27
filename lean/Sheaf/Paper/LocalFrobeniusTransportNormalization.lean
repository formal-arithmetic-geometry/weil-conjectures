/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.AlgebraicGeometry.FrobeniusFactorization
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.PointSectionsFiniteReduction
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.IntegralPointTransportTowerRealization
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Sheaf.TraceFormula.PointTransportComposition
public import Sheaf.Paper.FrobeniusCoefficientReductionCoherence
import Sheaf.SixFunctors.FrobeniusFixedPoints
import Sheaf.SixFunctors.SchemeGaloisCoefficientChange

/-!
# Rational-point transport and scheme-Frobenius normalization

Source: blueprint main-20261015, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final sentence and extracted local comparison
(blueprint: lem-trf-local-frobenius-transport-normalization).

## Main definitions

* `LocalFrobeniusTransport.finiteTransport`: successive point restrictions and return.
* `LocalFrobeniusTransport.finiteNormalized`: canonical fixed-point rho and kappa.
* `LocalFrobeniusTransport.strictMap`: the uniquely characterized whole quotient map.
* `LocalFrobeniusTransport.integralTransport` and `rationalTransport`: successive
  point transports, with the strict-system-normalized composition comparisons.
* `LocalFrobeniusTransport.Normalization`: all naturality, normalization, strict
  realization and coefficient-extension equations of the node.

## Main statements

* `localFrobeniusTransportNormalization`: the complete local normalization statement.

Positive indices are represented by successors. The direct-composite presentation
of a pullback power is used where stated; its canonical compositor is included in
both transport recipes. Derived-category instances preserve the point-fibre sizes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

namespace LocalFrobeniusTransport

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Exact point sections with the localization sizes fixed by pointFiniteFibre.
Source: blueprint trace-transport, point-fibre convention
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteSectionsDerived (n : ℕ) :=
  @Functor.mapDerivedCategory
    (integralOperationsFiniteModules l E (Spec (.of D.k)) n) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))

/-- The semilinear return equation for the induced rational point.
Source: blueprint trace-transport, final paragraph
(blueprint: lem-trf-local-frobenius-transport-normalization).
Proof: Frobenius fixes the specified finite subfield pointwise. The model and closure
projections of the two maps agree; the universal property of the fibre product concludes. -/
theorem returnEquation (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :
    ((pointFrobeniusAut D) ^ m).hom ≫ localExtensionPoint D X₀ m hm y =
      localExtensionPoint D X₀ m hm y ≫ ((End.of (D.geometricGaloisFrobenius X₀)) ^ m) := by
  sorry

/-- The scheme-Frobenius fixed-point equation, including nonminimal periods.
Source: blueprint trace-transport, final paragraph
(blueprint: lem-trf-local-frobenius-transport-normalization).
Proof: the q^m-power map fixes every coefficient of the specified rational point.
Compare both projections of the geometric fibre product. -/
theorem fixedEquation (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :
    localExtensionPoint D X₀ m hm y ≫ D.schemeFrobeniusIterate X₀ m =
      localExtensionPoint D X₀ m hm y := by
  sorry

/-- Canonical finite compositor around the semilinear return square.
Source: Stacks 0D6D; blueprint trace-transport, final paragraph
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteReturn (n m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :=
  proEtaleConstantRingPullbackComposition ((pointFrobeniusAut D) ^ m).hom
      (localExtensionPoint D X₀ m hm y) (Padic.coefficientExtensionRing l E (n + 1)) ≪≫
    eqToIso (congrArg
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)))
      (returnEquation D X₀ m hm y)) ≪≫
    (proEtaleConstantRingPullbackComposition (localExtensionPoint D X₀ m hm y)
      ((End.of (D.geometricGaloisFrobenius X₀)) ^ m)
      (Padic.coefficientExtensionRing l E (n + 1))).symm

/-- The finite J_y functor, read in the ambient module derived category. Its restriction
is the recorded bounded finite-cohomology fibre functor, with the same objects and maps.
Source: blueprint trace-transport, definition of J
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteFibre (n m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :
    proEtaleDerivedCategory (D.geometricFiber X₀).left
        (Padic.coefficientExtensionRing l E (n + 1)) ⥤
      @DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) _ _
          (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
      (localExtensionPoint D X₀ m hm y) ⋙
    (finiteSectionsDerived D l E n)

/-- Successive finite point transports, each changed to the constant-ring pullback
model before the next step. The canonical compositor joins the successive pullbacks;
no transport along a power is substituted for the successive one-step maps.
Source: blueprint trace-transport, definition of t and finite normalization
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finitePointIterate (n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :
    (r : ℕ) → (finiteSectionsDerived D l E n).obj N ⟶
      (finiteSectionsDerived D l E n).obj
        ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
          ((pointFrobeniusAut D) ^ (r + 1)).hom).obj N)
  | 0 =>
    frobeniusPointTransportFinite D l hl E n N ≫
      (finiteSectionsDerived D l E n).map
        ((pointPowerPullbackModel l E n (frobeniusPointIso D).hom).hom.app N ≫
          eqToHom (congrArg
            (fun f ↦ (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1)) f).obj N)
            (congrArg Iso.hom (pow_one (pointFrobeniusAut D))).symm))
  | r + 1 =>
    frobeniusPointTransportFinite D l hl E n N ≫
      (finiteSectionsDerived D l E n).map
        ((pointPowerPullbackModel l E n (frobeniusPointIso D).hom).hom.app N) ≫
      finitePointIterate n
        ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
          (frobeniusPointIso D).hom).obj N) r ≫
      (finiteSectionsDerived D l E n).map
        ((proEtaleConstantRingPullbackComposition
          ((pointFrobeniusAut D) ^ (r + 1)).hom (frobeniusPointIso D).hom
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app N ≫
          eqToHom (congrArg
            (fun f ↦ (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1)) f).obj N)
            (congrArg Iso.hom (pow_succ' (pointFrobeniusAut D) (r + 1))).symm))

/-- The m successive point transports followed by the canonical return compositor.
The predecessor index is used only to present a positive number of steps; the equality
(m-1)+1=m supplies the canonical reindexing to the node's power.
Source: blueprint trace-transport, definition of t
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteTransport (n m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm)
    (K : proEtaleDerivedCategory (D.geometricFiber X₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :
    (finiteFibre D l E X₀ n m hm y).obj K ⟶
      (finiteFibre D l E X₀ n m hm y).obj
        ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
          ((End.of (D.geometricGaloisFrobenius X₀)) ^ m)).obj K) :=
  finitePointIterate D l hl E n
      ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
        (localExtensionPoint D X₀ m hm y)).obj K) (m - 1) ≫
    (finiteSectionsDerived D l E n).map
      (eqToHom (congrArg
        (fun r ↦ (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1))
          ((pointFrobeniusAut D) ^ r).hom).obj
            ((proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1))
              (localExtensionPoint D X₀ m hm y)).obj K))
        (Nat.sub_add_cancel hm)) ≫
        (finiteReturn D l E X₀ n m hm y).hom.app K)

/-- The fixed-point identification rho, using precisely Phi^m ybar = ybar.
Source: blueprint trace-transport, definition of rho
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteRho (n m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm)
    (K : proEtaleDerivedCategory (D.geometricFiber X₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  (finiteSectionsDerived D l E n).map
    ((eqToIso (congrArg
      (fun f ↦ (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).obj K)
      (fixedEquation D X₀ m hm y).symm)).hom ≫
      (proEtaleConstantRingPullbackComposition (localExtensionPoint D X₀ m hm y)
        (D.schemeFrobeniusIterate X₀ m)
        (Padic.coefficientExtensionRing l E (n + 1))).inv.app K)

/-- The specified multiplicative kappa, without an arbitrary scalar rescaling.
Source: blueprint trace-transport, finite normalization
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteKappa (n m : ℕ) (hm : 1 ≤ m) :=
  letI : Fact (l ≠ D.p) := ⟨hl⟩
  D.canonicalSchemeGaloisComparison X₀ (Padic.coefficientExtensionRing l E (n + 1))
    (FiniteFieldDatum.frobeniusCoherenceAnnihilator l E D n) m hm

/-- The finite normalized map J(kappa) after rho, in Lean composition order.
Source: blueprint trace-transport, finite normalization display
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteNormalized (n m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm)
    (K : proEtaleDerivedCategory (D.geometricFiber X₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  finiteRho D l E X₀ n m hm y K ≫
    (finiteFibre D l E X₀ n m hm y).map ((finiteKappa D l hl E X₀ n m hm).hom.app K)

/-- The exact source single-complex comparison for finite fibre evaluation.
Source: Stacks 015F; blueprint trace-transport, degreewise calculation
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteSingleFibre (n : ℕ) {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y
      (Padic.coefficientExtensionRing l E (n + 1)))) :=
  (finiteSectionsDerived D l E n).mapIso
      (((proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategorySingleFunctor 0).app M) ≪≫
    (@Functor.mapDerivedCategorySingleFunctor _ _ _ (HasDerivedCategory.standard _)
      _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
      (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
      (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
      (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1))) 0).app
        ((proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f).obj M)

/-- The single-complex functor with precisely the point-fibre localization.
Source: Stacks 015F; blueprint trace-transport, degreewise calculation
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
abbrev finiteModuleSingle (n : ℕ) :=
  @DerivedCategory.singleFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _) 0

/-- The actual term map of either finite recipe, in the direct-composite presentation.
Taking the preimage under the fully faithful single-complex functor retains the
specified ordinary map; it makes no choice of a homotopy class representative.
Source: blueprint trace-transport, degreewise strict-system calculation
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def finiteOrdinary (normalized : Bool) (n m : ℕ) (hm : 1 ≤ m)
    (y : D.extensionPoints X₀ m hm)
    (M : proEtaleRingModules (D.geometricFiber X₀).left
      (proEtaleConstantRing (D.geometricFiber X₀).left
        (Padic.coefficientExtensionRing l E (n + 1)))) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1))
          (localExtensionPoint D X₀ m hm y)).obj M) ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1))
          (localExtensionPoint D X₀ m hm y ≫
            (End.of (D.geometricGaloisFrobenius X₀)) ^ m)).obj M) :=
  (finiteModuleSingle l E n).preimage
    ((finiteSingleFibre D l E n (localExtensionPoint D X₀ m hm y) M).inv ≫
      (if normalized then
        finiteNormalized D l hl E X₀ n m hm y ((DerivedCategory.singleFunctor _ 0).obj M)
      else finiteTransport D l hl E X₀ n m hm y ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
      (finiteSectionsDerived D l E n).map
        ((proEtaleConstantRingPullbackComposition (localExtensionPoint D X₀ m hm y)
          ((End.of (D.geometricGaloisFrobenius X₀)) ^ m)
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app
            ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
      (finiteSingleFibre D l E n
        (localExtensionPoint D X₀ m hm y ≫ ((End.of (D.geometricGaloisFrobenius X₀)) ^ m)) M).hom)

/-- The actual evaluated strict quotient tower of pullback along f.
Source: Stacks 0941; blueprint trace-transport, simultaneous-reduction paragraph
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def strictTower {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y) :=
  integralOperationsPullbackTowerFunctor l E f ⋙
    (Functor.whiskeringRight _ _ _).obj
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ))

/-- The degreewise formula specifying each of the two whole strict maps. Bool false
means point transport; true means the fixed-point rho followed by the canonical kappa.
The ordinary presentation comparisons preserve tensor units and all quotient transitions.
Source: blueprint trace-transport, Steps 3--5
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def StrictFormula (normalized : Bool) (m : ℕ) (hm : 1 ≤ m)
    (y : D.extensionPoints X₀ m hm)
    (U : strictTower D l E (localExtensionPoint D X₀ m hm y) ⟶
      strictTower D l E
        (localExtensionPoint D X₀ m hm y ≫
          ((End.of (D.geometricGaloisFrobenius X₀)) ^ m))) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules l E (D.geometricFiber X₀).left) ℤ)
    (n : ℕ) (i : ℤ)
    (x : (((strictTower D l E (localExtensionPoint D X₀ m hm y)).obj P).obj
      (Opposite.op n)).X i),
    (((U.app P).app (Opposite.op n)).f i).hom x =
      ((integralFinitePullbackModel l E
          (localExtensionPoint D X₀ m hm y ≫
            ((End.of (D.geometricGaloisFrobenius X₀)) ^ m)) n).inv.app
        (((unrestrictedIntegralFiniteComplex l E (D.geometricFiber X₀).left n).obj P).X i)).val.app
          (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))
        ((finiteOrdinary D l hl E X₀ normalized n m hm y
          (((unrestrictedIntegralFiniteComplex l E (D.geometricFiber X₀).left n).obj P).X i)).hom
          (((integralFinitePullbackModel l E (localExtensionPoint D X₀ m hm y) n).hom.app
            (((unrestrictedIntegralFiniteComplex l E
              (D.geometricFiber X₀).left n).obj P).X i)).val.app
              (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))) x))

/-- Each recipe gives one actual strict map of the simultaneous quotient complexes.
Source: blueprint trace-transport, Steps 3--5
(blueprint: lem-trf-local-frobenius-transport-normalization).
Proof: restrictions, comma insertions and the tensor-unit coefficient map are linear
and natural in the sheaf. The canonical relative-Frobenius trivialization is natural
in coefficient quotients. Both recipes commute with differentials and quotient arrows,
so they define the displayed natural chain map of whole towers. The single-complex
functor is fully faithful; its preimage in finiteOrdinary is precisely that sheaf map.
The formula on every degree and section determines the strict map uniquely. -/
theorem strictRecipe_existsUnique (normalized : Bool) (m : ℕ) (hm : 1 ≤ m)
    (y : D.extensionPoints X₀ m hm) :
    ∃! U : strictTower D l E (localExtensionPoint D X₀ m hm y) ⟶
      strictTower D l E
        (localExtensionPoint D X₀ m hm y ≫ ((End.of (D.geometricGaloisFrobenius X₀)) ^ m)),
      StrictFormula D l hl E X₀ normalized m hm y U := by
  sorry

/-- The uniquely specified strict map; no data is selected from a mere existence result.
Source: blueprint trace-transport, Steps 3--5
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def strictMap (normalized : Bool) (m : ℕ) (hm : 1 ≤ m)
    (y : D.extensionPoints X₀ m hm) :=
  (strictRecipe_existsUnique D l hl E X₀ normalized m hm y).exists.choose

/-- The positive-power presentation agrees with the ordinary endomorphism power.
Source: blueprint trace-transport, finite-iteration identifications
(blueprint: lem-trf-local-frobenius-transport-normalization).
Proof: at exponent one both sides are f. The recurrence composes by f; the power
successor equation identifies the two expressions at the next exponent. -/
theorem positivePower_eq {Y : Scheme.{u}} (f : Y ⟶ Y) (r : ℕ) :
    localPositivePower f r = (End.of f) ^ (r + 1) := by
  sorry

/-- The 1-s endomorphism of the evaluated strict tower.
Source: Stacks 0941 (blueprint: lem-trf-local-frobenius-transport-normalization). -/
def strictEnd {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((strictTower D l E f).obj P).obj (Opposite.op n))
    (integralOperationsTowerStep ((strictTower D l E f).obj P))

/-- The same 1-s before exact point sections.
Source: Stacks 0941 (blueprint: lem-trf-local-frobenius-transport-normalization). -/
def sheafEnd {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (Opposite.op n))
    (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P))

/-- The point-module localization already used by the integral fibre.
Source: Stacks 015F (blueprint: lem-trf-local-frobenius-transport-normalization). -/
abbrev integralModuleQ :=
  @DerivedCategory.Q
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- Exact point evaluation, with its recorded localization comparison.
Source: Stacks 015F (blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralSectionsFactors :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) (pointIntegralSectionsAdditive l E D.k)
    (pointFibreIntegralLimits D l E) (pointFibreIntegralColimits D l E)

/-- Point sections commute with the specified Roos cone, with both components fixed.
Source: Stacks 0941; blueprint trace-transport, Step 6
(blueprint: lem-trf-local-frobenius-transport-normalization).
Proof: products of completed module sheaves are sectionwise, and point sections
preserve these products. Identify the unshifted and shifted product coordinates by
evaluation, with the same 1-s and the same mapping-cocone signs. These identifications
are chain isomorphisms natural in P. The two coordinate equations determine them uniquely. -/
theorem sectionsRoos_existsUnique {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y) :
    ∃! β : integralOperationsPullbackComplexFunctor l E f ⋙
        (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) ≅
      strictTower D l E f ⋙ integralOperationsRoosFunctor,
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫
            (CochainComplex.mappingCocone.fst
              (strictEnd D l E f P)).f i ≫
            (Pi.π (fun j ↦ ((strictTower D l E f).obj P).obj (Opposite.op j)) n).f i =
          (pointIntegralSections l E D.k).map
            ((CochainComplex.mappingCocone.fst
              (sheafEnd D l E f P)).f i ≫
              (Pi.π (fun j ↦
                ((integralOperationsPullbackTowerFunctor l E f).obj P).obj
                  (Opposite.op j)) n).f i)) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫
            (CochainComplex.mappingCocone.snd
              (strictEnd D l E f P)).v
                  i (i - 1) (by omega) ≫
            (Pi.π (fun j ↦ ((strictTower D l E f).obj P).obj (Opposite.op j)) n).f (i - 1) =
          (pointIntegralSections l E D.k).map
            ((CochainComplex.mappingCocone.snd
              (sheafEnd D l E f P)).v
                    i (i - 1) (by omega) ≫
              (Pi.π (fun j ↦
                ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (Opposite.op j)) n).f
                  (i - 1))) := by
  sorry

/-- The sectionwise, two-coordinate comparison for the actual shifted cone.
Source: blueprint trace-transport, Step 6
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def sectionsRoos {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y) :=
  (sectionsRoos_existsUnique D l E f).exists.choose

/-- The canonical pointwise realization comparison on any flat-term K-flat representative.
Source: blueprint trace-transport, Step 6
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralModel {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullback l E f).mapIso e.symm ≪≫
        (integralDerivedPullbackComparison l E f).app P) ≪≫
    (integralSectionsFactors D l E).app
      ((integralOperationsPullbackComplexFunctor l E f).obj P.obj) ≪≫
    (integralModuleQ l E).mapIso ((sectionsRoos D l E f).app P.obj)

section Integral

variable (C : IntegralComparisonSystem.{u} l)

/-- The strict-system-normalized compositor, in the full constructible category.
Source: Stacks 099N, 0D6D; blueprint trace-transport, specified-family paragraph
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralComposition {V W Z : Scheme.{u}}
    [hV : ∀ v : V, Invertible (l : V.residueField v)]
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (@constructibleIntegralPullback l _ E _ _ _ _ _ (h ≫ k) hZ hV).obj K ≅
      (@constructibleIntegralPullback l _ E _ _ _ _ _ h hZ hW).obj
        ((@constructibleIntegralPullback l _ E _ _ _ _ _ k hW hV).obj K) :=
  { hom := ObjectProperty.homMk
      (@integralComparisonComposition l _ E _ _ _ C V W Z hV hW hZ h k K).hom
    inv := ObjectProperty.homMk
      (@integralComparisonComposition l _ E _ _ _ C V W Z hV hW hZ h k K).inv }

/-- Rationalize exactly the specified integral compositor, retaining its object comparisons.
Source: blueprint trace-transport, rationalization paragraph
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalComposition {V W Z : Scheme.{u}}
    [hV : ∀ v : V, Invertible (l : V.residueField v)]
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfRationalConstructibleCategory l E V) :
    (@rationalDerivedPullback l _ E _ _ _ _ _ (h ≫ k) hZ hV).obj K ≅
      (@rationalDerivedPullback l _ E _ _ _ _ _ h hZ hW).obj
        ((@rationalDerivedPullback l _ E _ _ _ _ _ k hW hV).obj K) :=
  @localPullbackObjectIso l _ E _ _ _ _ _ (h ≫ k) hZ hV K ≪≫
    (sfRationalConstructibleLocalization l E Z).mapIso
      (@integralComposition l _ E _ _ _ C V W Z hV hW hZ h k K.obj) ≪≫
    (@localPullbackObjectIso l _ E _ _ _ _ _ h hZ hW
      ((sfRationalConstructibleLocalization l E W).obj
        ((@constructibleIntegralPullback l _ E _ _ _ _ _ k hW hV).obj K.obj))).symm ≪≫
    (@rationalDerivedPullback l _ E _ _ _ _ _ h hZ hW).mapIso
      (@localPullbackObjectIso l _ E _ _ _ _ _ k hW hV K).symm

section Scalar

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] M)

/-- The rational pullback/scalar comparison determined by the stipulated integral formula.
Source: blueprint trace-transport, specified-family paragraph
(blueprint: lem-trf-local-frobenius-transport-normalization).
Proof: rationalize integralComparisonScalar, which is lambda followed by mu inverse.
The object formulas identify the two endpoints. Naturality extends from integral
maps to pure tensors by linearity and then to all Hom elements by additivity.
The component formula determines the comparison uniquely. -/
theorem rationalScalar_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! a : rationalDerivedPullback l E f ⋙
        sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι ≅
      sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι ⋙
        rationalDerivedPullback l M f,
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (a.hom.app K) ((sfRationalConstructibleLocalization l M X).map
          (ObjectProperty.homMk
            (X := (integralComparisonConstructibleScalar l E M ι X).obj
              ((constructibleIntegralPullback l E f).obj K.obj))
            (Y := (constructibleIntegralPullback l M f).obj
              ((integralComparisonConstructibleScalar l E M ι Y).obj K.obj))
            (integralComparisonScalar l E M ι C f K.obj).hom)) := by
  sorry

/-- The pullback/scalar comparison in the specified strict-system family.
Source: blueprint trace-transport, definition of d and b
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  (rationalScalar_existsUnique l E C M ι f).exists.choose

end Scalar

/-- Fraction-field tensor with the same small derived-category universes as the point
fibre. Source: blueprint trace-transport, Step 7
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def pointFractionDerived :=
  @Functor.mapDerivedCategory
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} E))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E))
    (pointIntegralToFieldAdditive l E)
    (pointFibreFractionLimits l E) (pointFibreFractionColimits l E)

variable [hpoint : ∀ x : Spec (.of D.k),
    Invertible (l : (Spec (.of D.k)).residueField x)]

/-- Identify the actual rational point fibre with the size descent of integral sections
followed by tensor with E. All arrows here are the recorded object and size comparisons.
Source: blueprint trace-transport, Step 7
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalFibreModel {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :=
  (pointRationalFibre D l hl E).mapIso
      (@localPullbackObjectIso l _ E _ _ _ _ _ f hpoint hY K) ≪≫
    pointRationalFibreObjIso D l hl E
      ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
        ((@constructibleIntegralPullback l _ E _ _ _ _ _ f hpoint hY).obj K.obj))

/-- Successive integral point transports, identified with the pullback by g_s^(r+1).
All compositors are the entire-system realization formulas, not independently chosen
reductionwise isomorphisms. Source: blueprint trace-transport, Step 2
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralPointIterate (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (r : ℕ) → (pointIntegralFibre D l hl E).obj N ⟶
      (pointIntegralFibre D l hl E).obj
        ((constructibleIntegralPullback l E
          (localPositivePower (frobeniusPointIso D).hom r)).obj N)
  | 0 => frobeniusPointTransportIntegralConstructible D l hl E N
  | r + 1 =>
    frobeniusPointTransportIntegralConstructible D l hl E N ≫
      integralPointIterate
        ((constructibleIntegralPullback l E (frobeniusPointIso D).hom).obj N) r ≫
      (pointIntegralFibre D l hl E).map
        (integralComposition l E C (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointIso D).hom N).inv

/-- Successive rational point transports; the integral compositor is rationalized at
all recursive steps. Source: blueprint trace-transport, Steps 2 and 7
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalPointIterate (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (r : ℕ) → (pointRationalFibre D l hl E).obj N ⟶
      (pointRationalFibre D l hl E).obj
        ((rationalDerivedPullback l E
          (localPositivePower (frobeniusPointIso D).hom r)).obj N)
  | 0 => localPointTransport l E D hl N
  | r + 1 =>
    localPointTransport l E D hl N ≫
      rationalPointIterate ((rationalDerivedPullback l E (frobeniusPointIso D).hom).obj N) r ≫
      (pointRationalFibre D l hl E).map
        (rationalComposition l E C (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointIso D).hom N).inv

variable [hspace : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x)]

/-- The integral comparison around a return square, for the stated positive-power model.
Source: blueprint trace-transport, Step 2
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralReturn (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom r ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom r)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (integralComposition l E C (hV := hspace) (hW := hpoint) (hZ := hpoint)
        (localPositivePower (frobeniusPointIso D).hom r) z K).symm ≪≫
    eqToIso (congrArg
      (fun f ↦ (@constructibleIntegralPullback l _ E _ _ _ _ _ f hpoint hspace).obj K) w) ≪≫
    integralComposition l E C (hV := hspace) (hW := hspace) (hZ := hpoint)
      z (localPositivePower (D.geometricFrobenius X₀).hom r) K

/-- The integral J_y, using the dependency's derived-complete constructible category.
Source: blueprint trace-transport, definition of J
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralFibre (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  @constructibleIntegralPullback l _ E _ _ _ _ _ z hpoint hspace ⋙ pointIntegralFibre D l hl E

/-- Integral t is the iterated point transport followed by the specified compositor.
Source: blueprint trace-transport, definition of t
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralTransport (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom r ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom r)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  integralPointIterate D l hl E C (hpoint := hpoint)
      ((@constructibleIntegralPullback l _ E _ _ _ _ _ z hpoint hspace).obj K)
      r ≫
    (pointIntegralFibre D l hl E).map
      (integralReturn D l E X₀ C (hpoint := hpoint) (hspace := hspace) r z w K).hom

/-- J_y at the raw rationalized constructible stage, with its actual finite-dimensional
point-fibre target. Source: blueprint trace-transport, definition of J
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalFibre (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ z hpoint hspace ⋙ pointRationalFibre D l hl E

/-- Canonical rational return comparison, obtained from the specified integral system.
Source: blueprint trace-transport, Step 7
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalReturn (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom r ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom r)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (rationalComposition l E C (hV := hspace) (hW := hpoint) (hZ := hpoint)
        (localPositivePower (frobeniusPointIso D).hom r) z K).symm ≪≫
    eqToIso (congrArg
      (fun f ↦ (@rationalDerivedPullback l _ E _ _ _ _ _ f hpoint hspace).obj K) w) ≪≫
    rationalComposition l E C (hV := hspace) (hW := hspace) (hZ := hpoint)
      z (localPositivePower (D.geometricFrobenius X₀).hom r) K

/-- Rational t uses the rationalized integral iota and the rationalized strict compositor.
Source: blueprint trace-transport, Steps 2 and 7
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalTransport (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom r ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom r)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  rationalPointIterate D l hl E C (hpoint := hpoint)
      ((@rationalDerivedPullback l _ E _ _ _ _ _ z hpoint hspace).obj K)
      r ≫
    (pointRationalFibre D l hl E).map
      (rationalReturn D l E X₀ C (hpoint := hpoint) (hspace := hspace) r z w K).hom

/-- The return equation in the positive-power convention used by the recursive recipe.
Source: blueprint trace-transport, Step 1
(blueprint: lem-trf-local-frobenius-transport-normalization).
Proof: apply returnEquation with m=r+1. The positive-power recurrence and the
homomorphism from automorphisms to endomorphisms identify its two powers with these. -/
theorem positiveReturnEquation (r : ℕ)
    (y : D.extensionPoints X₀ (r + 1) (Nat.succ_pos r)) :
    localPositivePower (frobeniusPointIso D).hom r ≫
        localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y =
      localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y ≫
        localPositivePower (D.geometricFrobenius X₀).hom r := by
  sorry

/-- Integral t in the direct-composite pullback presentation, before the final c(y,g).
Source: blueprint trace-transport, Steps 2 and 6
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralDirect (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom r ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom r)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  integralPointIterate D l hl E C (hpoint := hpoint)
      ((@constructibleIntegralPullback l _ E _ _ _ _ _ z hpoint hspace).obj K)
      r ≫
    (pointIntegralFibre D l hl E).map
      ((integralComposition l E C (hV := hspace) (hW := hpoint) (hZ := hpoint)
        (localPositivePower (frobeniusPointIso D).hom r) z K).inv ≫
        eqToHom (congrArg
          (fun f ↦ (@constructibleIntegralPullback l _ E _ _ _ _ _ f hpoint hspace).obj K)
          (w.trans (congrArg (fun g ↦ z ≫ g)
            (positivePower_eq (D.geometricFrobenius X₀).hom r)))))

/-- The rational direct-composite presentation uses the very same canonical identifications.
Source: blueprint trace-transport, Step 7
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalDirect (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom r ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius X₀).hom r)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  rationalPointIterate D l hl E C (hpoint := hpoint)
      ((@rationalDerivedPullback l _ E _ _ _ _ _ z hpoint hspace).obj K)
      r ≫
    (pointRationalFibre D l hl E).map
      ((rationalComposition l E C (hV := hspace) (hW := hpoint) (hZ := hpoint)
        (localPositivePower (frobeniusPointIso D).hom r) z K).inv ≫
        eqToHom (congrArg (fun f ↦ (@rationalDerivedPullback l _ E _ _ _ _ _ f hpoint hspace).obj K)
          (w.trans (congrArg (fun g ↦ z ≫ g)
            (positivePower_eq (D.geometricFrobenius X₀).hom r)))))

/-- The normalized integral right-hand side is realization of the actual whole strict
map built from kappa and rho, transported by the prescribed cone comparisons.
Source: blueprint trace-transport, Step 6
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def integralNormalized (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) :=
  (integralModel D l E (localExtensionPoint D X₀ m hm y) K P e).hom ≫
    (integralModuleQ l E).map
      (integralOperationsRoosMap ((strictMap D l hl E X₀ true m hm y).app P.obj)) ≫
    (integralModel D l E
      (localExtensionPoint D X₀ m hm y ≫ (End.of (D.geometricGaloisFrobenius X₀)) ^ m)
      K P e).inv

/-- Rationalize the entire integral normalized map, rather than its separate reductions.
Source: blueprint trace-transport, Step 7
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalNormalized (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj.obj) :=
  (rationalFibreModel D l hl E (hpoint := hpoint)
      (localExtensionPoint D X₀ m hm y) (hY := hspace) K).hom ≫
    (pointFibreSizeDescent E).map
      (ObjectProperty.homMk
        (X := pointFibreRationalLarge D l hl E
          ((constructibleIntegralPullback l E (localExtensionPoint D X₀ m hm y)).obj K.obj))
        (Y := pointFibreRationalLarge D l hl E
          ((constructibleIntegralPullback l E
            (localExtensionPoint D X₀ m hm y ≫
              (End.of (D.geometricGaloisFrobenius X₀)) ^ m)).obj K.obj))
        ((pointFractionDerived l E).map
            (integralNormalized D l hl E X₀ m hm y K.obj P e))) ≫
    (rationalFibreModel D l hl E (hpoint := hpoint)
      (localExtensionPoint D X₀ m hm y ≫ (End.of (D.geometricGaloisFrobenius X₀)) ^ m)
      (hY := hspace) K).inv

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] M)

/-- b is pullback comparison followed by the inverse point-sections comparison, in
composition order. Source: blueprint trace-transport, definition of b
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def rationalFibreScalar (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (pointRationalFibreScalarIso D l hl E M ι).inv.app
      ((@rationalDerivedPullback l _ E _ _ _ _ _ z hpoint hspace).obj K) ≫
    (pointRationalFibre D l hl M).map
      ((rationalScalar l E C M ι z (hX := hpoint) (hY := hspace)).hom.app K)

end Integral

/-- All clauses of rational-point transport normalization. The index r denotes m=r+1;
finite coefficient index n denotes A_(E,n+1). The invertibility instances are constructed
from l≠p and are not added hypotheses. The integral and rational equations use the
direct-composite presentation; the final canonical compositor recovers J_y G^m.
Source: blueprint trace-transport, final paragraph and extracted normalization lemma
(blueprint: lem-trf-local-frobenius-transport-normalization). -/
def Normalization (C : IntegralComparisonSystem.{u} l) (r : ℕ)
    (y : D.extensionPoints X₀ (r + 1) (Nat.succ_pos r)) : Prop :=
  letI pointInvertible := frobeniusPointPrimeInvertible D l hl
  letI spaceInvertible := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  (∀ (n : ℕ)
    (K L : (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber X₀).left).FullSubcategory) (a : K ⟶ L),
    (finiteFibre D l E X₀ n (r + 1) (Nat.succ_pos r) y).map a.hom ≫
        finiteTransport D l hl E X₀ n (r + 1) (Nat.succ_pos r) y L.obj =
      finiteTransport D l hl E X₀ n (r + 1) (Nat.succ_pos r) y K.obj ≫
        (finiteFibre D l E X₀ n (r + 1) (Nat.succ_pos r) y).map
          ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
            ((End.of (D.geometricGaloisFrobenius X₀)) ^ (r + 1))).map a.hom)) ∧
  (∀ (n : ℕ)
    (K : (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber X₀).left).FullSubcategory),
    finiteTransport D l hl E X₀ n (r + 1) (Nat.succ_pos r) y K.obj =
      finiteNormalized D l hl E X₀ n (r + 1) (Nat.succ_pos r) y K.obj) ∧
  (∀ P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory,
    (strictMap D l hl E X₀ false (r + 1) (Nat.succ_pos r) y).app P.obj =
      (strictMap D l hl E X₀ true (r + 1) (Nat.succ_pos r) y).app P.obj) ∧
  (∀ (K L : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) (a : K ⟶ L),
    (integralFibre D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible)
        (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)).map a ≫
        integralTransport D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C r
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
          (positiveReturnEquation D X₀ r y) L =
      integralTransport D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C r
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
          (positiveReturnEquation D X₀ r y) K ≫
        (integralFibre D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible)
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)).map
            ((constructibleIntegralPullback l E
              (localPositivePower (D.geometricFrobenius X₀).hom r)).map a)) ∧
  (∀ (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj),
    (integralDirect D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C r
      (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
      (positiveReturnEquation D X₀ r y) K).hom =
        integralNormalized D l hl E X₀ (r + 1) (Nat.succ_pos r) y K P e) ∧
  (∀ (K L : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) (a : K ⟶ L),
    (rationalFibre D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible)
        (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)).map a ≫
        rationalTransport D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C r
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
          (positiveReturnEquation D X₀ r y) L =
      rationalTransport D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C r
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
          (positiveReturnEquation D X₀ r y) K ≫
        (rationalFibre D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible)
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)).map
            ((rationalDerivedPullback l E
              (localPositivePower (D.geometricFrobenius X₀).hom r)).map a)) ∧
  (∀ (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj.obj),
    rationalDirect D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C r
      (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
      (positiveReturnEquation D X₀ r y) K =
        rationalNormalized D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible)
          (r + 1) (Nat.succ_pos r) y K P e) ∧
  (∀ (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] M)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left),
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (rationalTransport D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C r
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
          (positiveReturnEquation D X₀ r y) K) ≫
      rationalFibreScalar D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C M ι
        (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
        ((rationalDerivedPullback l E
          (localPositivePower (D.geometricFrobenius X₀).hom r)).obj K) ≫
      (rationalFibre D l hl M X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible)
        (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)).map
          ((rationalScalar l E C M ι
            (localPositivePower (D.geometricFrobenius X₀).hom r)).hom.app K) =
      rationalFibreScalar D l hl E X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C M ι
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y) K ≫
        rationalTransport D l hl M X₀
          (hpoint := pointInvertible) (hspace := spaceInvertible) C r
          (localExtensionPoint D X₀ (r + 1) (Nat.succ_pos r) y)
          (positiveReturnEquation D X₀ r y)
          ((sfRationalScalarExtension l E (D.geometricFiber X₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).obj K))

end LocalFrobeniusTransport
/-- Rational-point transport is natural, canonically normalized by scheme Frobenius,
compatible as an equality of whole strict quotient maps, and compatible with every
finite coefficient embedding. Integral and rational normalization is realization
and rationalization of that actual strict equality, with no Tor-amplitude bound.
Source: blueprint main-20261015, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final sentence
(blueprint: lem-trf-local-frobenius-transport-normalization).

Proof (the DAG proof plan):

1. Write $g=g_X$, $h=g_s^m$, $H=\operatorname{Fr}^{(q^m)}_X$ and
$r=\operatorname{Fr}^{(q^m)}_s=h^{-1}$. The last equality follows from the arithmetic/geometric
inverse convention in [def-weil-frobenius-detailed]. By [thm-trf-frobenius-fixed-points], the
$k$-point $\bar y$ obtained from the specified rational point satisfies $\Phi^m\bar y=\bar y$.
The factorization [prop-trf-frobenius-factorization] and the inverse convention give
$\Phi^m=g^mH$. Absolute Frobenius is natural: on affine rings this is the identity
$f(a^{q^m})=f(a)^{q^m}$, so $H\bar y=\bar y r$. Therefore $g^m\bar y r=\bar y$, and composition
with $h$ gives $g^m\bar y=\bar y h$. These are equalities of scheme maps; semilinear $g$ is not
being treated as a $k$-morphism.

2. Let $H_\Lambda=Lg_{s,\Lambda}^*$ and $P_\Lambda=L\bar y_\Lambda^*$. Define $I^{(0)}_N=1$ and
$I^{(j+1)}_N=\iota_{H_\Lambda^jN}\,I^{(j)}_N$, so
$I^{(m)}_N:\operatorname{Fib}_sN\to\operatorname{Fib}_sH_\Lambda^mN$. Each $\iota$ is the
specified map of [def-weil-frobenius-point-transport]. By
[lem-weil-frobenius-point-transport-natural](2), induction gives
$\operatorname{Fib}_s(H_\Lambda^m v)I^{(m)}_N=I^{(m)}_{N'}\operatorname{Fib}_s(v)$ for every
$v:N\to N'$: apply the one-step naturality equation to $H_\Lambda^jv$ and compose with the
induction equation. The scheme equality in Step 1 gives a natural comparison
$v_{\Lambda,K}:H_\Lambda^mP_\Lambda K\xrightarrow{\sim}P_\Lambda G_\Lambda^mK$ using
[lem-weil-pbc-proetale-derived-pullback-composition] at finite level,
[lem-pod-integral-pullback-composition] integrally, and their rationalizations. Put
$t_{y,m,K}=\operatorname{Fib}_s(v_{\Lambda,K})I^{(m)}_{P_\Lambda K}$. Naturality of $v$ and the
displayed induction equation give exactly $J_y(G_\Lambda^mu)t_{y,m,K}=t_{y,m,L}J_y(u)$.

3. At finite coefficients the point calculation can be made on a sheaf $N$, then degreewise on a
complex. By [lem-weil-proetale-isomorphism-inverse-image](1), $(Lh^*N)(s)=N(s\xrightarrow{h}s)$.
Under this identification, restriction followed by colimit insertion in
[def-weil-frobenius-point-transport] is $\operatorname{res}_h:N(s,1)\to N(s,h)$; composing $m$
such maps is restriction along $h=g_s^m$. Let $\tau_s:Lr^*\to1$ be the canonical
absolute-Frobenius trivialization specified by [lem-pur-frobenius-trivialization-pullback], with
exponent $am$. At the final object its value on a sheaf $M$ is $(\operatorname{res}_r^M)^{-1}$:
the relative-Frobenius identification in that statement, adjointed to inverse image and
evaluated at the final object, is the inverse of restriction along the isomorphism
$r:(s,r)\to(s,1)$. For $M=Lh^*N$, this restriction identifies with
$\operatorname{res}_r:N(s,h)\to N(s,1)$; its inverse is $\operatorname{res}_h$. Thus under
$Lr^*Lh^*N\cong N$ one has $\Gamma(s,\tau_{s,Lh^*N})=I_N^{(m)}$. Exact constant-coefficient
pullback [prop-weil-pbc-proetale-constant-exact] and exact point sections
[lem-weil-point-proetale-sections-exact] make this a degreewise identity computing the derived
maps. No scalar is inserted.

4. Expand the canonical comparison specified in the statement: with $\tau_X:LH^*\to1$, it is
$\kappa_K^{(m)}=(\tau_X)_{L(g^m)^*K}\circ c_{H,g^m,K}$, where $c_{H,g^m}:L\Phi^{m*}\to
LH^*L(g^m)^*$ is the canonical composition map. This is the cancellation of absolute Frobenius
in $\Phi^m=g^mH$ from [prop-trf-scheme-galois-comparison], with its required canonical
normalization. Apply the pullback-naturality equation of
[lem-pur-frobenius-trivialization-pullback] to $u=\bar y$ and exponent $am$. It identifies
$P_\Lambda(\tau_X)$ with $\tau_sP_\Lambda$ under $H\bar y=\bar y r$. Use
[lem-weil-pbc-proetale-derived-pullback-composition] to identify the successive pullbacks. After
precomposition with the fixed-point identification $\rho_{y,m,K}$, the resulting map is
$\Gamma(s,\tau_{s,P_\Lambda L(g^m)^*K})$ with source identified with $P_\Lambda K$ through
$Lr^*H_\Lambda^m\cong1$ and $v_{\Lambda,K}$. Naturality of $\tau_s$ with respect to
$v_{\Lambda,K}$ and Step 3 give
$$J_{y,\Lambda}(\kappa_K^{(m)})\rho_{y,m,K}=\operatorname{Fib}_s(v_{\Lambda,K})I^{(m)}_{P_\Lambda
K}=t_{y,m,K}.$$
Here the canonical composition identifications on the two paths agree: on a pullback of a
section both send it to the same section on the iterated fiber product, with its same
projections. The termwise description in the cited composition statement computes those
identifications.

5. The equality of Step 4 holds before localizing complexes. For an integral object choose one
flat-term K-flat resolution $Q\to K$ by [lem-pc-kflat-resolution] and use the simultaneous
quotients $Q_n=Q\otimes(A_{E,n})_X$. They are K-flat with flat terms by
[lem-pur-kflat-change-of-rings]. Every restriction used in Step 3, every colimit coprojection,
and the relative-Frobenius isomorphisms specifying $\tau$ is a natural map of module sheaves,
hence commutes with $Q_{n+1}\to Q_n$. The coefficient factors send a tensor $x\otimes b$ to the
restriction of $x$ tensored with $b$; reduction before or after this map therefore gives the
same tensor. The termwise pullback-composition maps of
[lem-weil-pbc-proetale-derived-pullback-composition] have the same property. Consequently Step 4
is an equality of maps of these strict quotient diagrams, including their transitions. For
derived change of the finite coefficient ring, [lem-trf-scheme-galois-coefficient-change] gives
the equation for the specified $\kappa^{(m)}$, with no flatness or Tor-amplitude assumption; the
point comparison [lem-trf-point-sections-finite-reduction] applies because every reduction of an
integral constructible object is bounded by [def-weil-derived-complete-integral-detailed]; it
does not require a perfect complex. Thus the maps used here are compatible with both the strict
transitions and their canonical derived coefficient identifications.

6. For $N=P_{\mathcal O_E}K$, [lem-trf-integral-point-transport-tower-realization] identifies
each specified integral $\iota_{H_{\mathcal O_E}^jN}$ with realization of the actual
point-transport morphism of its coherent quotient tower. The formulas for $c$ and $\eta$ in
[lem-trf-integral-pullback-comparison-realization] identify the integral composition map itself
with realization of the strict termwise composition maps, including the comparison from the
realized iterated tower to the iterated completed pullback. Apply those formulas to the square
$g^m\bar y=\bar y h$ and to each splitting into successive pullbacks. The strict left-hand map
of Step 5 is the composite of these termwise composition maps and the finite point transports.
Its realization is therefore exactly $\operatorname{Fib}_s(v_{\mathcal
O_E,K})I^{(m)}_{P_{\mathcal O_E}K}$ of Step 2. The right-hand map realizes, by the same
specified composition identifications, to the stipulated realization of $J_y(\kappa^{(m)})\rho$.
Apply the functor $R\lim$ of [lem-weil-pbc-ringed-strict-tower-homotopy-limit] to the equality
of whole strict maps from Step 5. This proves the integral equality. No step infers an integral
equality solely from equal individual reductions, and no finite Tor-amplitude assumption enters.

7. By [def-weil-rationalization-karoubi] the objects at $E$ are the integral objects and their
morphisms are $\operatorname{Hom}_{\mathcal O_E}\otimes E$. By
[def-weil-frobenius-point-transport] the rational point transport is the scalar extension of the
integral transport. Applying rationalization to Step 6 gives the required normalization at $E$.
For rational naturality it suffices to take a morphism $f\otimes\lambda$: both sides of the
naturality equation of Step 2 become $\lambda$ times the rationalization of its integral
equation for $f$, by the linear formulas for pullback in [def-weil-derived-pullback-tensor-hom]
and for the point functor in [def-weil-finite-coefficient-point]. Additivity gives the equation
for every morphism. Thus this argument covers morphisms in the raw framework rationalization and
does not replace it by a larger category or invoke an idempotent completion.

8. Write $T_s$ for scalar extension on $s$, $a_K:T_sP_EK\to P_MTK$ for the pullback comparison,
and $\delta_N:T_sH_E^mN\to H_M^mT_sN$ for the iterated point pullback comparison. The
comparisons are now specified by [lem-trf-integral-pullback-comparison-realization], not
characterized by their individual reductions. Its composition/scalar equation, applied along the
two equal scheme maps $g^m\bar y=\bar y g_s^m$, and then along every splitting of $g^m$ and
$g_s^m$, gives
$$v_{M,TK}H_M^m(a_K)\delta_{P_EK}=P_M(d_K)a_{G_E^mK}T_s(v_{E,K}).$$
Indeed its left path first uses the scalar comparisons for the successive point pullbacks and
for $\bar y$, and then the compositor defining $v_M$; its right path first uses $v_E$, then the
scalar comparison for $\bar y$ and the successive $g$ pullbacks. The lemma's equation
interchanges a scalar comparison with each compositor, and its equality-of-scheme-maps and
associativity clauses identify the two paths. These are equalities of the specified simultaneous
quotient-diagram maps and hence their integral realizations; the rationalization clause gives
the displayed equation. The identity and coefficient-tower clauses use the completion-normalized
tensor associator, matching that in [lem-weil-point-sections-scalar-extension]. No assertion
about the unaccepted proof of lem-pur-integral-operations-scalar-extension is used.

9. Let $\beta_N:\operatorname{Fib}_{s,E}N\otimes_E M\to\operatorname{Fib}_{s,M}T_sN$ be the
inverse of the rational sections comparison of [lem-weil-point-sections-scalar-extension]. The
scalar-compatibility clause of [lem-weil-frobenius-point-transport-natural](2) gives, for one
step, $\operatorname{Fib}_{s,M}(\delta_N)\beta_{H_EN}(\iota_N\otimes M)=\iota_{T_sN}\beta_N$.
Apply that equation in turn to $N,H_EN,\ldots,H_E^{m-1}N$; naturality of $\iota$ moves each
intermediate pullback comparison across the next transport. The adjacent comparison factors
compose to the iterated $\delta_N$, giving
$$\operatorname{Fib}_{s,M}(\delta_N)\beta_{H_E^mN}(I_N^{(m)}\otimes M)=I_{T_sN}^{(m)}\beta_N.$$
The point comparisons are exactly those of Step 8: the strict-system choices and their scalar
associator are specified by [lem-trf-integral-pullback-comparison-realization]. For identity and
successive field extensions the equations use the identity and associator clauses of
[lem-weil-point-sections-scalar-extension] and [lem-pur-integral-operations-scalar-extension],
so the same induction gives those compatibilities for every $m$.

10. By its definition in the statement, $b_K=\operatorname{Fib}_{s,M}(a_K)\beta_{P_EK}$. Expand
$t_{y,m,K}=\operatorname{Fib}_{s,E}(v_{E,K})I^{(m)}_{P_EK}$ on the left-hand side of the desired
coefficient equation. Naturality of $\beta$ with respect to $v_{E,K}$ rewrites it as
$$\operatorname{Fib}_{s,M}\!\left(P_M(d_K)a_{G_E^mK}T_s(v_{E,K})\right)
\beta_{H_E^mP_EK}(I^{(m)}_{P_EK}\otimes
M).$$
Substitute the square proved in Step 8 and the iterated point equation of Step 9. The result is
$$\operatorname{Fib}_{s,M}\!\left(v_{M,TK}H_M^m(a_K)\right)I^{(m)}_{T_sP_EK}\beta_{P_EK}.$$
Naturality of $I^{(m)}$ for $a_K$, proved in Step 2, makes this
$\operatorname{Fib}_{s,M}(v_{M,TK})I^{(m)}_{P_MTK}\operatorname{Fib}_{s,M}(a_K)\beta_{P_EK}
=t_{y,m,TK}b_K$.
This proves the final displayed equation. The identity and tower identifications remain the
specified ones because each substitution uses the same comparisons as Steps 8 and 9. The
naturality of $\beta$ used here is part of [lem-weil-point-sections-scalar-extension].
-/
theorem localFrobeniusTransportNormalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (C : IntegralComparisonSystem.{u} l) (r : ℕ)
    (y : D.extensionPoints X₀ (r + 1) (Nat.succ_pos r)) :
    LocalFrobeniusTransport.Normalization D l hl E X₀ C r y := by
  sorry

end WeilConjectures
