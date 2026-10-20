/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.Paper.ProjectiveBundleFormula
public import Sheaf.Paper.SupportedHomPullback
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Supported splitting prescribed by a coefficient projection

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`thm-pur-localized-top-chern.proof.md`, Step 1, supported-Hom and projection-formula
calculation (blueprint: def-pur-supported-projection-splitting).

## Main definitions

* `supportedProjectionRetraction`: the equation for the coefficient retraction.
* `supportedProjectionHomRetraction`: its induced supported-Hom map.
* `supportedProjectionPullback`: homology of the actual derived kernel pullback.
* `supportedProjectionSplitting`: the normalized additive splitting predicate.

This definition asserts no existence. Its argument prescribes the coefficient
projection, and its equations require the specified induced splitting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- Compose the three specified coefficient-unit comparisons in a fixed category.
Source: blueprint Step 1, coefficient-unit comparison
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionComposeUnitIso {C : Type v} [Category.{w} C] {X Y Z W : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ W) : X ≅ W := a ≪≫ b ≪≫ c

/-- The published constant module sheaf is the sheaf monoidal unit.
The identity comparison exposes this definitional identification once.
Source: blueprint Step 1, untwisted coefficient
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionEtaleUnitIso (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.ordinaryFiniteConstant A T ≅
      𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := Iso.refl _

/-- The coefficient unit in the derived monoidal coordinates, using the canonical
single-functor and comparison unit maps. Source: blueprint Step 1, projection formula
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionUnitIso (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit A T) ≅ 𝟙_ (ProEtale.ModuleDerivedCategory T A) :=
  supportedProjectionComposeUnitIso (C := ProEtale.ModuleDerivedCategory T A)
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
      T).mapDerivedCategorySingleFunctor 0).app _)
    ((DerivedCategory.singleFunctor _ 0).mapIso
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapIso
        (supportedProjectionEtaleUnitIso A T) ≪≫ ProEtale.comparisonUpperStarUnitIso A T))
    (DerivedCategory.singleFunctorObjUnitIso.{u + 1, u + 1, u + 2} _)

/-- Canonical unit action in any monoidal category, retaining the given unit comparison.
Source: blueprint Step 1, coefficient multiplication
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionMonoidalUnitAction {C : Type v} [Category.{w} C] [MonoidalCategory C]
    (U : C) (u : U ≅ 𝟙_ C) (K : C) : U ⊗ K ⟶ K :=
  u.hom ▷ K ≫ (λ_ K).hom

/-- Adjunction followed by a specified retraction, in fixed categorical coordinates.
Source: blueprint Step 1, supported-Hom adjunction calculation
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionAdjunctRetraction
    {C : Type v} [Category.{w} C] {D : Type v₁} [Category.{w₁} D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) {M N W : C} {M' V : D}
    (c : L.obj M ⟶ M') (alpha : M' ⟶ V) (d : V ⟶ L.obj N)
    (r : R.obj (L.obj N) ⟶ W) : M ⟶ W :=
  adj.homEquiv M (L.obj N) (c ≫ alpha ≫ d) ≫ r

/-- Shift an adjunction through the specified exact-functor comparison, then retract.
Source: blueprint Step 1, supported-Hom adjunction calculation
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionShiftedAdjunct
    {C : Type v} [Category.{w} C] [HasShift C ℤ]
    {D : Type v₁} [Category.{w₁} D] [HasShift D ℤ]
    (L S : C ⥤ D) (R : D ⥤ C) [S.CommShift ℤ] [R.CommShift ℤ]
    (adj : L ⊣ R) (e : L ≅ S) (M N : C) (M' : D) (b : ℤ)
    (c : L.obj M ⟶ M') (alpha : M' ⟶ (S.obj N)⟦b⟧)
    (r : R.obj (L.obj N) ⟶ N) : M ⟶ N⟦b⟧ :=
  supportedProjectionAdjunctRetraction L R adj c alpha
    ((S.commShiftIso b).inv.app N ≫ e.inv.app (N⟦b⟧))
    (R.map (e.hom.app (N⟦b⟧) ≫ (S.commShiftIso b).hom.app N ≫
        (e.inv.app N)⟦b⟧') ≫
      (R.commShiftIso b).hom.app (L.obj N) ≫ r⟦b⟧')

/-- Apply the canonical shifted adjunction to a supported Hom class.
Source: blueprint Step 1, supported-Hom calculation
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionHomRetractionRaw (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (f : T' ⟶ T)
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (M' : Sheaf (Scheme.ProEt.topology T') (ModuleCat.{u + 1} A))
    (c : (ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj M ⟶ M')
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} A))) (b : ℤ)
    (rK : (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K.obj) ⟶
        K.obj)
    (alpha : (DerivedCategory.singleFunctor _ 0).obj M' ⟶
      ((ProEtale.upperStar (ModuleCat.{u + 1} A)
        f).mapDerivedCategoryPlus.obj K).obj⟦b⟧) :
    (DerivedCategory.singleFunctor _ 0).obj M ⟶ K.obj⟦b⟧ :=
  supportedProjectionShiftedAdjunct
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    ((DerivedCategory.singleFunctor _ 0).obj M) K.obj
    ((DerivedCategory.singleFunctor _ 0).obj M') b
    ((ProEtale.singleFunctorCompLeftDerivedUpperStarIso
      (ModuleCat.{u + 1} A) f).hom.app M ≫ (DerivedCategory.singleFunctor _ 0).map c)
    alpha rK

/-- Specialize the shifted adjunction to the canonical closed-support exchange.
Source: blueprint Step 1, supported-Hom calculation
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionHomRetraction (P : PurityFiniteSetting.{u})
    {Z T Z' T' : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (i' : Z' ⟶ T') [IsClosedImmersion i'] (f : T' ⟶ T)
    (e : proEtaleSupportHomTransport P i i' f) :=
  supportedProjectionHomRetractionRaw P.Coefficient f (proEtaleSupportHomPair P i).supported
    (proEtaleSupportHomPair P i').supported
    (e.closedIso (hB := Scheme.ProEt.isContinuous_overPullback f)).hom

/-- The projection-retraction equation, with the canonical unit actions.
Source: blueprint Step 1, projection formula and coefficient multiplication
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionEquation {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {D : Type v₁} [Category.{w₁} D] [MonoidalCategory D]
    (L : C ⥤ D) (R : D ⥤ C) (U : C) (V : D) (K : C)
    (u : U ≅ 𝟙_ C) (v : V ≅ 𝟙_ D)
    (pi : R.obj V ⊗ K ⟶ R.obj (V ⊗ L.obj K))
    (rho : R.obj V ⟶ U) (rK : R.obj (L.obj K) ⟶ K) : Prop :=
  pi ≫ R.map (supportedProjectionMonoidalUnitAction V v (L.obj K)) ≫ rK =
    rho ▷ K ≫ supportedProjectionMonoidalUnitAction U u K

/-- Specialize the categorical equation to the published pro-etale projection map.
Keeping the coefficient category explicit preserves the original site universes.
Source: blueprint Step 1, canonical projection formula
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionFormulaEquation
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
    {T T' : Scheme.{u}} (f : T' ⟶ T)
    (U : DerivedCategory (Sheaf (Scheme.ProEt.topology T) A))
    (V : DerivedCategory (Sheaf (Scheme.ProEt.topology T') A))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) A))
    (u : U ≅ 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) A)))
    (v : V ≅ 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T') A)))
    (rho : (ProEtale.lowerStar A f).rightDerivedFunctor.obj V ⟶ U)
    (rK : (ProEtale.lowerStar A f).rightDerivedFunctor.obj
      ((ProEtale.upperStar A f).leftDerivedFunctor.obj K) ⟶ K) : Prop :=
  supportedProjectionEquation (ProEtale.upperStar A f).leftDerivedFunctor
    (ProEtale.lowerStar A f).rightDerivedFunctor U V K u v
    (((ProEtale.rightDerivedLowerStarProjectionMap A f).app V).app K) rho rK

/-- The projection-formula equation with the actual counit-defined projection map.
Source: blueprint Step 1, projection formula
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionRetractionRaw (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {T T' : Scheme.{u}} (f : T' ⟶ T) (K : ProEtale.ModuleDerivedCategory T A)
    (rho : (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit A T')) ⟶
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit A T))
    (rK : (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K) ⟶ K) : Prop :=
  supportedProjectionFormulaEquation (ModuleCat.{u + 1} A) f
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit A T))
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit A T')) K
    (supportedProjectionUnitIso A T) (supportedProjectionUnitIso A T') rho rK

/-- Specialize the projection equation to the actual finite coefficient quotient.
The finite-ring instance is the published coefficient-extension theorem and size lift.
Source: blueprint Step 1, finite coefficients in the projection formula
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionRetraction (P : PurityFiniteSetting.{u})
    {T T' : Scheme.{u}} (f : T' ⟶ T)
    (K : ProEtale.ModuleDerivedCategory T P.Coefficient)
    (rho : (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
      (P.projectiveBundleUnit T') ⟶ P.projectiveBundleUnit T)
    (rK : (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj K) ⟶ K) :
    Prop :=
  letI : Finite P.Coefficient := @Finite.of_equiv P.Coefficient P.Ring
    (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos)
    Equiv.ulift.symm
  letI : IsNoetherianRing P.Coefficient :=
    isNoetherian_of_finite P.Coefficient P.Coefficient
  supportedProjectionRetractionRaw P.Coefficient f K rho rK

/-- Take homology of a map in the fixed bounded-below derived category.
The derived-category instance is an explicit parameter, retaining its original size.
Source: blueprint Step 1, supported pullback
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionHomologyMap {A : Type v} [Category.{w} A] [Abelian A]
    [hD : HasDerivedCategory.{w} A] {K L : DerivedCategory.Plus A} (h : K ⟶ L) (b : ℤ) :
    (DerivedCategory.Plus.homologyFunctor A b).obj K ⟶
      (DerivedCategory.Plus.homologyFunctor A b).obj L :=
  (DerivedCategory.Plus.homologyFunctor A b).map h

/-- The canonical supported pullback, as homology of the published derived kernel map.
The supported-Hom pullback theorem identifies this actual map with pullback of Hom
for etale-origin coefficients through the normalized identifications.
Source: blueprint Step 1, supported-Hom pullback
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionPullback (P : PurityFiniteSetting.{u})
    {Z T Z' T' : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (i' : Z' ⟶ T') [IsClosedImmersion i'] (f : T' ⟶ T)
    (e : proEtaleSupportHomTransport P i i' f)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient))) (b : ℤ)
    (x : (proEtaleSupportHomPair P i).group K b) :
    (proEtaleSupportHomPair P i').group
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategoryPlus.obj K) b :=
  supportedProjectionHomologyMap (A := ModuleCat.{u + 1} P.Coefficient)
    (hD := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
      (ModuleCat.{u + 1} P.Coefficient))
    ((e.derivedMap (hB := Scheme.ProEt.isContinuous_overPullback f)).app K) b x

/-- An additive splitting with its normalization in two specified Hom coordinates.
Source: blueprint Step 1, additive supported-Hom splitting
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionAdditiveSplitting
    {G : Type v} [AddCommGroup G] {H : Type w} [AddCommGroup H]
    {M : Type v₁} {N : Type w₁}
    (chi : G → M) (chi' : H → N) (pull : G → H) (ret : N → M) : Prop :=
  ∃ s : H →+ G, (∀ x : G, s (pull x) = x) ∧ ∀ y : H, chi (s y) = ret (chi' y)

/-- The prescribed supported splitting induced by a coefficient projection.
`componentCondition` fixes that projection on the actual Chern components in the
flag application below. The remaining equations spell out the projection formula,
normalized supported Hom, actual kernel pullback, and the additive left inverse.
Source: blueprint Step 1, supported projection splitting
(blueprint: def-pur-supported-projection-splitting). -/
def supportedProjectionSplitting (P : PurityFiniteSetting.{u})
    {Z T Z' T' : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (i' : Z' ⟶ T') [IsClosedImmersion i'] (f : T' ⟶ T)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient))) (b : ℤ)
    (componentCondition : ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      f).rightDerivedFunctor.obj (P.projectiveBundleUnit T') ⟶
        P.projectiveBundleUnit T) → Prop) : Prop :=
    ∃ chi : (proEtaleSupportHomPair P i).Identification,
    ∃ chi' : (proEtaleSupportHomPair P i').Identification,
    ∃ e : proEtaleSupportHomTransport P i i' f,
    ∃ rho : (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        f).rightDerivedFunctor.obj
          (P.projectiveBundleUnit T') ⟶
        P.projectiveBundleUnit T,
    componentCondition rho ∧
    ∃ rK : (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        f).rightDerivedFunctor.obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            f).leftDerivedFunctor.obj
              K.obj) ⟶ K.obj,
    P.supportedProjectionRetraction f
      K.obj rho rK ∧
    supportedProjectionAdditiveSplitting (chi.chi K b)
      (chi'.chi ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        f).mapDerivedCategoryPlus.obj K) b)
      (P.supportedProjectionPullback i i' f e K b)
      (P.supportedProjectionHomRetraction i i' f e K b rK)

end WeilConjectures.PurityFiniteSetting
