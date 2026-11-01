/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.TwistedCoordinateSectionSign
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateIdealFrame
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! # The coordinate localization splice and its exceptional transpose

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
rank-one paragraph, and Stacks Tag 0A45
(blueprint: def-pur-coordinate-localization-splice).

The class below is constructed from the open-closed coefficient sequence and
Kummer class of t. It makes no reference to the Cartier class or to an orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
-- Reuse the instance witnesses of the published coordinate chart.
set_option linter.auxLemma false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

-- Use the same derived-category instances as the published single comparisons.
set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.DerivedCategoryModule._proof_1 Etale.DerivedCategoryModule._proof_2
  AlgebraicGeometry.ProEtale.ModuleDerivedCategory._proof_1
  AlgebraicGeometry.ProEtale.ModuleDerivedCategory._proof_2

attribute [local implicit_reducible] Etale.cartierAbelianPro Etale.cartierAbelianEtale
  Etale.cartierAbelianGroups

attribute [local implicit_reducible] catToReflQuiver

namespace WeilConjectures.PurityFiniteSetting

/-- The unmodified coefficient localization sequence on the affine line.
Source: Stacks Tag 0A45 (blueprint: def-pur-coordinate-localization-splice). -/
def coordinateLocalizationSequence (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Etale.openClosedShortComplex (ModuleCat.{u + 1} P.Coefficient) (openImmersion T) (zeroSection T)
    (disjoint_range_of_range_eq_compl _ _ (coordinateLocalization_complement T))
    (P.constantEtale (Line T))

/-- Exactness of the coefficient localization sequence.
Source: Stacks Tag 0A45 (blueprint: def-pur-coordinate-localization-splice).
Proof: apply the open-closed exact sequence to the complementary coordinate pair. -/
theorem coordinateLocalizationSequence_shortExact (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) : (P.coordinateLocalizationSequence T).ShortExact := by
  exact Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} P.Coefficient) (openImmersion T)
    (zeroSection T) (P.constantEtale (Line T)) (coordinateLocalization_complement T)

/-- Extend the coordinate Kummer class by zero, then apply the twist counit. The
source retains the inverse-image constant appearing in the localization sequence.
Source: Stacks Tag 0A45 (blueprint: def-pur-coordinate-localization-splice). -/
def coordinateLocalizationOpenClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) :
    Ext (P.coordinateLocalizationSequence T).X₁ (P.twistEtale h (Line T)) 1 := by
  let j := openImmersion T
  let J := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) j
  let hr := P.exponent_isUnit (Line T) (lineProjection T ≫ aT)
  letI := P.isIso_twistEtalePullback h j hr
  let e := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) j).app
    (ModuleCat.of P.Coefficient P.Coefficient)
  let ε := J.map (inv (P.twistEtalePullback h j)) ≫
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) j).counit.app (P.twistEtale h (Line T))
  exact (Ext.mk₀ (J.map e.hom)).comp
    (((P.kummerEtale h (Punctured T)
      (P.exponent_isUnit (Punctured T) (puncturedProjection T ≫ aT))
      (coordinateUnit T)).mapExactFunctor J).comp (Ext.mk₀ ε) (add_zero 1)) (zero_add 1)

/-- The positive coordinate boundary as the actual Yoneda localization splice.
The closed source is identified using the inverse canonical constant comparison.
Source: Stacks Tag 0A45 (blueprint: def-pur-coordinate-localization-splice). -/
def coordinateLocalizationClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) :
    Ext ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (zeroSection T)).obj (P.constantEtale T))
      (P.twistEtale h (Line T)) 2 :=
  ((Ext.mk₀ ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T)).map
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) (zeroSection T)).app
      (ModuleCat.of P.Coefficient P.Coefficient)).inv)).comp
    (P.coordinateLocalizationSequence_shortExact T).extClass (zero_add 1)).comp
      (P.coordinateLocalizationOpenClass h T aT) (rfl : 1 + 1 = 2)

/-- Derived realization of the negative coordinate localization splice.
Source: Stacks Tag 0A45 (blueprint: def-pur-coordinate-localization-splice). -/
def coordinateLocalizationOrdinaryNegative (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) :=
  Etale.supportedExactDerivedMap (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
    (P.constantEtale T) (P.twistEtale h (Line T)) (-P.coordinateLocalizationClass h T aT)

attribute [local irreducible] coordinateLocalizationClass coordinateLocalizationOrdinaryNegative
attribute [local irreducible] coordinateCartierOrdinary

/-- The ordinary closed exceptional transpose, with its actual published adjunction.
Source: the coordinate orientation chart
(blueprint: def-pur-coordinate-localization-splice).
The explicit local witnesses retain the published etale realization before forming
single objects, derived functors and the Hom equivalence. -/
@[irreducible] def coordinateOrdinaryTranspose (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :=
  letI := coordinateCartierOrdinary._proof_2 P T
  letI := coordinateCartierOrdinary._proof_3 P T
  letI := coordinateCartierOrdinary._proof_4 P T
  letI := coordinateCartierOrdinary._proof_5 P T
  letI := coordinateCartierOrdinaryAdjunct._proof_1 P T
  letI := coordinateCartierOrdinaryAdjunct._proof_2 T
  letI := coordinateCartierOrdinaryAdjunct._proof_3 P
  letI := coordinateCartierOrdinaryAdjunct._proof_4 P
  letI := coordinateCartierOrdinaryAdjunct._proof_5 P
  letI := coordinateCartierOrdinaryAdjunct._proof_6 T
  fun
    (f : (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T)).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj (P.constantEtale T)) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj (P.twistEtale h (Line T)))⟦(2 : ℤ)⟧) ↦
      ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient
        (zeroSection T)).ofNatIsoLeft
          (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))).homEquiv _ _ f
/-- Specialization of the ordinary transpose to the existing Cartier arrow.
Source: the published coordinate Cartier adjunct
(blueprint: def-pur-coordinate-localization-splice).
Proof: unfold the two constructions; their adjunction and instance witnesses agree. -/
theorem coordinateOrdinaryTranspose_cartier (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (hI : (zeroSection T).ker.IsInvertible) :
    coordinateOrdinaryTranspose P h T (P.coordinateCartierOrdinary h T aT hI) =
      P.coordinateCartierOrdinaryAdjunct h T aT hI := by
  unfold coordinateOrdinaryTranspose coordinateCartierOrdinaryAdjunct
  rfl
/-- Transport an ordinary arrow through the actual single, closed adjunction,
shift and comparison-unit maps of the published coordinate Cartier adjunct.
Source: the coordinate orientation chart
(blueprint: def-pur-coordinate-localization-splice).
The input is an arbitrary ordinary supported arrow; the formula uses its closed
transpose, followed by the same five canonical comparison factors as the chart. -/
@[irreducible] def coordinateOrdinaryToGysin (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :=
  letI := coordinateCartierOrdinaryAdjunct._proof_1 P T
  letI := coordinateCartierOrdinaryAdjunct._proof_2 T
  letI := coordinateCartierOrdinaryAdjunct._proof_3 P
  letI := coordinateCartierOrdinaryAdjunct._proof_4 P
  letI := coordinateCartierOrdinaryAdjunct._proof_5 P
  letI := coordinateCartierOrdinaryAdjunct._proof_6 T
  letI := coordinateCartierAdjunct._proof_1 P T
  letI := coordinateCartierAdjunct._proof_2 P T
  letI := coordinateCartierAdjunct._proof_3 P T
  letI := coordinateCartierAdjunct._proof_4 P T
  letI := coordinateCartierAdjunct._proof_5 P T
  letI := coordinateCartierAdjunct._proof_6 P T
  letI := coordinateCartierAdjunct._proof_7 P T
  letI := coordinateCartierAdjunct._proof_10 P T
  letI := coordinateCartierAdjunct._proof_11 P T
  letI := coordinateCartierAdjunct._proof_12 P T
  letI := coordinateCartierAdjunct._proof_13 P T (2 : ℤ)
  fun f ↦
    ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategorySingleFunctor
        0).inv.app (P.constantEtale T) ≫
        (nu P T).map
          (coordinateOrdinaryTranspose P h T f) ≫
        (nu P T).map
          (((Etale.rightDerivedUpperShriek P.Coefficient
            (zeroSection T)).commShiftIso (2 : ℤ)).hom.app
              (P.gysinEtaleInput h T).obj) ≫
        ((nu P T).commShiftIso (2 : ℤ)).hom.app _ ≫
        (shiftFunctor _ (2 : ℤ)).map
          (boundedSiteRho P.Coefficient
            (Etale.rightDerivedUpperShriek P.Coefficient (zeroSection T))
            (P.gysinEtaleInput h T).obj)

/-- Specialization of ordinary-to-Gysin transport to the existing Cartier adjunct.
Source: the published coordinate Cartier arrow
(blueprint: def-pur-coordinate-localization-splice).
Proof: use the ordinary transpose specialization and unfold the five outer factors. -/
theorem coordinateOrdinaryToGysin_cartier (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (hI : (zeroSection T).ker.IsInvertible) :
    coordinateOrdinaryToGysin P h T (P.coordinateCartierOrdinary h T aT hI) =
      P.coordinateCartierAdjunct h T aT hI := by
  with_unfolding_all rfl
/-- Uniqueness of normalized ordinary boundaries converts the negative localization
normalization into equality of actual derived arrows.
Source: Stacks Tags 03PL and 0A45
(blueprint: def-pur-coordinate-localization-splice).
Proof: apply uniqueness to the negative localization Ext class, then apply the
same exact-single comparison and Ext realization to the equal classes. -/
theorem coordinateCartierOrdinary_eq_of_normalization (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (hI : (zeroSection T).ker.IsInvertible)
    (hκ : Etale.SupportedKummerBoundary P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h) (zeroSection T) hI
      (P.exponent_isUnit (Line T) (lineProjection T ≫ aT))
      (-P.coordinateLocalizationClass h T aT)) :
    P.coordinateCartierOrdinary h T aT hI = P.coordinateLocalizationOrdinaryNegative h T aT := by
  let H := Etale.ordinary_supported_kummer_uniqueBoundary (Line T) P.exponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) P.Coefficient
    (P.exponent_coefficient_eq_zero h)
    (P.exponent_isUnit (Line T) (lineProjection T ≫ aT)) (zeroSection T) hI
  have he : H.exists.choose = -P.coordinateLocalizationClass h T aT :=
    H.unique H.exists.choose_spec hκ
  unfold coordinateCartierOrdinary coordinateLocalizationOrdinaryNegative
  exact congrArg (fun κ ↦ Etale.supportedExactDerivedMap
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T))
      (P.constantEtale T) (P.twistEtale h (Line T)) κ) he

/-- The positive localization class in the published exceptional coordinates,
formed by negating the exceptional transpose of the negative ordinary splice.
Source: the localization construction and the canonical closed exceptional transpose
(blueprint: def-pur-coordinate-localization-splice). -/
def coordinateLocalizationGysin (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) :
    P.derivedSheaf h T false ⟶ P.gysinValue h T :=
  letI := coordinateCartierAdjunct._proof_1 P T
  letI := coordinateCartierAdjunct._proof_2 P T
  letI : AddCommGroup (P.derivedSheaf h T false ⟶ P.gysinValue h T) :=
    @Preadditive.homGroup (DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))) _
      inferInstance _ _
  Neg.neg (P.coordinateOrdinaryToGysin h T (P.coordinateLocalizationOrdinaryNegative h T aT))

end WeilConjectures.PurityFiniteSetting
