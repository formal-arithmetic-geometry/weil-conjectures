/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi

import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import Mathlib.CategoryTheory.Shift.Localization

/-! # Exactness of finite scalar extension

Source: blueprint `sec-smooth-purity/sk-prop-sf-pf-reduction`, order 1883
(blueprint: lem-weil-scalar-extension-exact-triangulated).
The shift comparison is specified on integral representatives, including its sign.
-/

@[expose] public section
set_option autoImplicit false

universe d u
open CategoryTheory TensorProduct

namespace WeilConjectures

section CommShiftHelpers

variable {C' D' : Type*} [Category* C'] [Category* D'] {A : Type*} [AddMonoid A]
  [HasShift C' A] [HasShift D' A]

/-- Two shift comparisons with the same components coincide.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem commShift_ext {G : C' ⥤ D'} (c₁ c₂ : G.CommShift A)
    (h : ∀ (a : A) (X : C'), (G.commShiftIso (self := c₁) a).hom.app X =
      (G.commShiftIso (self := c₂) a).hom.app X) : c₁ = c₂ := by
  cases c₁
  cases c₂
  congr
  funext a
  ext X
  exact h a X

/-- A shift comparison compatible with an isomorphism is the conjugated one.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem commShiftIso_hom_app_of_natTrans {F G : C' ⥤ D'} (e : F ≅ G)
    [F.CommShift A] [c : G.CommShift A] [h : NatTrans.CommShift e.hom A] (a : A) (X : C') :
    (G.commShiftIso a).hom.app X =
      e.inv.app (X⟦a⟧) ≫ (F.commShiftIso a).hom.app X ≫ (e.hom.app X)⟦a⟧' := by
  rw [← cancel_epi (e.hom.app (X⟦a⟧)), ← NatTrans.shift_app_comm, e.hom_inv_id_app_assoc]

/-- The inverse of an isomorphism whose forward map is an identity is an identity.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem inv_heq_id {X Y : C'} (e : X ≅ Y) (hXY : Y = X) (h : HEq e.hom (𝟙 X)) :
    HEq e.inv (𝟙 X) := by
  subst hXY
  have h' := eq_of_heq h
  apply heq_of_eq
  calc e.inv = e.inv ≫ e.hom := by rw [h', Category.comp_id]
    _ = 𝟙 _ := e.inv_hom_id

/-- A functor sends a morphism equal to an identity to an identity.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem map_heq_id (F : C' ⥤ D') {X Y : C'} (f : X ⟶ Y) (hXY : Y = X)
    (h : HEq f (𝟙 X)) : HEq (F.map f) (𝟙 (F.obj X)) := by
  subst hXY
  rw [eq_of_heq h, F.map_id]

end CommShiftHelpers

section IntegerShiftHelpers

variable {C' D' : Type*} [Category* C'] [Category* D'] [HasShift C' ℤ] [HasShift D' ℤ]

private theorem commShiftIso_zero_hom_app {G : C' ⥤ D'} [c : G.CommShift ℤ] (X : C') :
    (G.commShiftIso (0 : ℤ)).hom.app X = (Functor.CommShift.isoZero G ℤ).hom.app X := by
  rw [G.commShiftIso_zero]

private theorem commShiftIso_succ_hom_app {G : C' ⥤ D'} [c : G.CommShift ℤ] (a b : ℤ)
    (h : a + 1 = b) (X : C') :
    (G.commShiftIso b).hom.app X = G.map ((shiftFunctorAdd' C' a 1 b h).hom.app X) ≫
      (G.commShiftIso (1 : ℤ)).hom.app (X⟦a⟧) ≫ ((G.commShiftIso a).hom.app X)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' D' a 1 b h).inv.app (G.obj X) := by
  rw [G.commShiftIso_add' h]
  simp only [Functor.CommShift.isoAdd'_hom_app]

/-- A shift comparison for integer shifts is determined by its component at one.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: induction on the integer, using the addition coherence and faithfulness of the
shift by one for the negative direction. -/
private theorem commShift_ext_of_one {G : C' ⥤ D'} (c₁ c₂ : G.CommShift ℤ)
    (h : ∀ X : C', (G.commShiftIso (self := c₁) (1 : ℤ)).hom.app X =
      (G.commShiftIso (self := c₂) (1 : ℤ)).hom.app X) : c₁ = c₂ := by
  apply commShift_ext
  intro n
  induction n using Int.induction_on with
  | zero =>
    intro X
    rw [commShiftIso_zero_hom_app (c := c₁), commShiftIso_zero_hom_app (c := c₂)]
  | succ n ih =>
    intro X
    rw [commShiftIso_succ_hom_app (c := c₁) (n : ℤ) _ rfl,
      commShiftIso_succ_hom_app (c := c₂) (n : ℤ) _ rfl, h, ih]
  | pred n ih =>
    intro X
    have e := (commShiftIso_succ_hom_app (c := c₁) (-(n : ℤ) - 1) (-(n : ℤ))
      (by omega) X).symm.trans ((ih X).trans (commShiftIso_succ_hom_app (c := c₂)
        (-(n : ℤ) - 1) (-(n : ℤ)) (by omega) X))
    rw [h] at e
    simp only [cancel_epi, cancel_mono] at e
    exact (shiftFunctor D' (1 : ℤ)).map_injective e

end IntegerShiftHelpers

section ScalarLocalizationComparison

open CategoryTheory.Limits CategoryTheory.Pretriangulated

variable (R : Type*) [CommRing R] (C : Type*) [Category C]
  [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R)

/-- The comparison of raw scalar localization with the Verdier rationalization.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private noncomputable def scalarRationalComparison :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.induction_on with
    | zero => simp only [Limits.zero_comp, map_zero, Limits.zero_comp]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [Limits.comp_zero, map_zero, Limits.comp_zero]
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (ScalarLocalization.composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [ScalarLocalization.composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

/-- Raw scalar localization is a localization at the rationalization morphisms.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: the comparison with the Verdier rationalization is an equivalence compatible
with the two localization functors. -/
private theorem scalarLocalization_isLocalization :
    (ScalarLocalization.localization R C p).IsLocalization
      (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let E := scalarRationalComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := ScalarLocalization.localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, ScalarLocalization.localization, scalarRationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
    (Rationalization.W M C) Q E.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

end ScalarLocalizationComparison

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

section SubcategoryShift

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

private theorem ι_commShiftIso_hom_app {C' : Type*} [Category* C'] [HasShift C' ℤ]
    (R : ObjectProperty C') [R.IsStableUnderShift ℤ] (n : ℤ) (X : R.FullSubcategory) :
    (R.ι.commShiftIso n).hom.app X = 𝟙 _ := rfl

/-- The shift comparison of the restricted ordinary functor inherited from the ambient one.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem integralConstructibleScalar_liftCommShift_spec :
    (fun [commInst :
        (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ] ↦
      ∀ (n : ℤ) K,
        HEq (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso n).hom.app K).hom
          (((integralOrdinaryDerivedScalar l E L ι Y).commShiftIso n).hom.app K.obj))
      (commInst := (inferInstance :
        ((boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
          ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
            integralOrdinaryDerivedScalar l E L ι Y)
          (fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y
            K.obj K.property)).CommShift ℤ)) := by
  let P := boundedConstructibleDerivedCompleteIntegral D l hl L Y
  let Q := boundedConstructibleDerivedCompleteIntegral D l hl E Y
  let G := integralOrdinaryDerivedScalar l E L ι Y
  have hF : ∀ K : Q.FullSubcategory, P ((Q.ι ⋙ G).obj K) :=
    fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y K.obj K.property
  intro n K
  have h := NatTrans.shift_app_comm (P.liftCompιIso (Q.ι ⋙ G) hF).hom n K
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app,
    ι_commShiftIso_hom_app, ι_commShiftIso_hom_app] at h
  apply heq_of_eq
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.ι_map] at h
  refine Eq.trans ?_ (h.trans ?_)
  · erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
    try rfl
  · erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
    try rfl

end SubcategoryShift

/-- The full subcategory inherits the ordinary derived tensor shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: the ambient termwise exact tensor functor has its canonical derived shift
comparison. Full faithfulness of the inclusions lifts it uniquely. The ambient zero
and addition coherence equations imply the same equations after this lift. -/
theorem integralConstructibleScalarCommShift_existsUnique :
    ∃! c : (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ,
      (fun [commInst :
          (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ] ↦
        ∀ (n : ℤ) K,
          HEq (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso n).hom.app K).hom
            (((integralOrdinaryDerivedScalar l E L ι Y).commShiftIso n).hom.app K.obj))
        (commInst := c) := by
  refine existsUnique_of_exists_of_unique
    ⟨_, integralConstructibleScalar_liftCommShift_spec D l hl E Y L ι⟩ ?_
  intro c₁ c₂ h₁ h₂
  apply commShift_ext
  intro n K
  apply ObjectProperty.hom_ext
  exact eq_of_heq ((h₁ n K).trans (h₂ n K).symm)

/-- The uniquely normalized integral shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance integralConstructibleScalarCommShift :
    (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ :=
  (integralConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- The restricted ordinary functor is triangulated for its normalized shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: the normalized comparison is the one inherited from the ambient exact derived
functor, which is triangulated; the lift to triangulated full subcategories is too. -/
private theorem integralConstructibleScalar_isTriangulated :
    (integralConstructibleScalarExtension D l hl E L ι Y).IsTriangulated := by
  have hc : integralConstructibleScalarCommShift D l hl E Y L ι = _ :=
    (integralConstructibleScalarCommShift_existsUnique D l hl E Y L ι).unique
      (integralConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose_spec
      (integralConstructibleScalar_liftCommShift_spec D l hl E Y L ι)
  rw [hc]
  exact (inferInstance : ((boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
    ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
      integralOrdinaryDerivedScalar l E L ι Y)
    (fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y
      K.obj K.property)).IsTriangulated)

/-- The integral-to-rational square for the ordinary scalar functor, with identity
components. Source: blueprint order 1883
(blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private noncomputable def rationalOrdinaryLift :
    rationalConstructibleLocalization D l hl E Y ⋙ rationalOrdinaryScalarExtension D l hl E Y L ι ≅
      integralConstructibleScalarExtension D l hl E L ι Y ⋙
        rationalConstructibleLocalization D l hl L Y :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro K K' f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change rationalScalarHom D l hl E Y L ι K K'
        ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E)) ⊗ₜ f) =
      (1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ
        (integralConstructibleScalarExtension D l hl E L ι Y).map f
    exact ((rationalScalarHom_existsUnique D l hl E Y L ι K K').exists.choose_spec 1 f).trans
      (by rw [map_one]))

private theorem rationalOrdinaryLift_hom_app
    (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    (rationalOrdinaryLift D l hl E Y L ι).hom.app K = 𝟙 _ := rfl

private theorem rationalOrdinaryLift_inv_app
    (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    (rationalOrdinaryLift D l hl E Y L ι).inv.app K = 𝟙 _ := rfl

/-- The rational localization of the integral constructible category.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem rationalConstructibleLocalization_isLocalization :
    letI := fun n : ℤ ↦ integralConstructibleShift_linear l E Y D hl n
    (rationalConstructibleLocalization D l hl E Y).IsLocalization
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)) :=
  letI := fun n : ℤ ↦ integralConstructibleShift_linear l E Y D hl n
  scalarLocalization_isLocalization _ _ _

/-- The localized shift comparison of the rational ordinary functor, with its normalization
and its compatibility with the integral-to-rational square.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
private theorem rationalOrdinaryScalarCommShift_exists :
    ∃ c : (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst :
          (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        (∀ K, HEq
          (((rationalOrdinaryScalarExtension D l hl E Y L ι).commShiftIso (1 : ℤ)).hom.app K)
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L]
            (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso
              (1 : ℤ)).hom.app K.obj))) ∧
        NatTrans.CommShift (rationalOrdinaryLift D l hl E Y L ι).hom ℤ) (commInst := c) := by
  letI := fun n : ℤ ↦ integralConstructibleShift_linear l E Y D hl n
  let W := Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
  let LE := rationalConstructibleLocalization D l hl E Y
  let LL := rationalConstructibleLocalization D l hl L Y
  let Fi := integralConstructibleScalarExtension D l hl E L ι Y
  let Fr := rationalOrdinaryScalarExtension D l hl E Y L ι
  have : LE.IsLocalization W := rationalConstructibleLocalization_isLocalization D l hl E Y
  let : Localization.Lifting LE W (Fi ⋙ LL) Fr := ⟨rationalOrdinaryLift D l hl E Y L ι⟩
  let c : Fr.CommShift ℤ := Functor.commShiftOfLocalization LE W ℤ (Fi ⋙ LL) Fr
  refine ⟨c, ?_, NatTrans.commShift_iso_hom_of_localization LE W ℤ (Fi ⋙ LL) Fr⟩
  intro K
  obtain ⟨X⟩ := K
  have h1E := (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.1
  have h1L := (rationalTriangulationDatum D l hl L Y).choose_spec.choose_spec.1
  have hLE := (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.1
  have hLL := (rationalTriangulationDatum D l hl L Y).choose_spec.choose_spec.2.choose_spec.choose_spec.1
  have hc := Functor.commShiftOfLocalization_iso_hom_app LE W (Fi ⋙ LL) Fr (1 : ℤ) X
  rw [Functor.commShiftIso_comp_hom_app] at hc
  erw [rationalOrdinaryLift_hom_app, rationalOrdinaryLift_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hc
  refine HEq.trans (heq_of_eq hc) ?_
  have eqE : (LE.obj X)⟦(1 : ℤ)⟧ = LE.obj (X⟦(1 : ℤ)⟧) :=
    congrArg (fun G ↦ G.obj (LE.obj X)) h1E
  have eqL : (LL.obj (Fi.obj X))⟦(1 : ℤ)⟧ = LL.obj ((Fi.obj X)⟦(1 : ℤ)⟧) :=
    congrArg (fun G ↦ G.obj (LL.obj (Fi.obj X))) h1L
  have ha : HEq (Fr.map ((LE.commShiftIso (1 : ℤ)).inv.app X)) (𝟙 (Fr.obj (LE.obj (X⟦(1 : ℤ)⟧)))) :=
    map_heq_id Fr ((LE.commShiftIso (1 : ℤ)).inv.app X) eqE (inv_heq_id ((LE.commShiftIso (1 : ℤ)).app X) eqE (hLE X))
  have hb := hLL (Fi.obj X)
  refine (heq_comp (congrArg Fr.obj eqE) rfl eqL ha
    (heq_comp rfl rfl eqL HEq.rfl hb)).trans (heq_of_eq ?_)
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- The rational shift comparison is the integral one tensored with one.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: localize the integral shift comparison and inverse. Naturality on pure tensors
extends by additivity. The rational shift by one is the tensor-induced integral shift;
its localization comparison is the identity. Thus the displayed normalization holds.
Iteration and inverse shifts give a coherent comparison for every integer. A coherent
comparison for integer shifts is determined by its component at one, proving uniqueness. -/
theorem rationalOrdinaryScalarCommShift_existsUnique :
    ∃! c : (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst :
          (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        ∀ K, HEq
          (((rationalOrdinaryScalarExtension D l hl E Y L ι).commShiftIso (1 : ℤ)).hom.app K)
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L]
            (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso
              (1 : ℤ)).hom.app K.obj))) (commInst := c) := by
  obtain ⟨c, hc, -⟩ := rationalOrdinaryScalarCommShift_exists D l hl E Y L ι
  refine existsUnique_of_exists_of_unique ⟨c, hc⟩ ?_
  intro c₁ c₂ h₁ h₂
  exact commShift_ext_of_one c₁ c₂ (fun K ↦ eq_of_heq ((h₁ K).trans (h₂ K).symm))

/-- The normalized rational shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalOrdinaryScalarCommShift :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ :=
  (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- The rational ordinary functor is exact for its normalized shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: every rational distinguished triangle is isomorphic to the localization of an
integral one. The integral-to-rational square commutes with shifts, and the restricted
integral functor and the target localization are triangulated. -/
private theorem rationalOrdinaryScalar_exact :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).IsTriangulated := by
  obtain ⟨c, hc, hn⟩ := rationalOrdinaryScalarCommShift_exists D l hl E Y L ι
  have heq : rationalOrdinaryScalarCommShift D l hl E Y L ι = c :=
    (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L ι).unique
      (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L ι).exists.choose_spec hc
  subst heq
  have := integralConstructibleScalar_isTriangulated D l hl E Y L ι
  have : (rationalConstructibleLocalization D l hl L Y).IsTriangulated :=
    (rationalTriangulationDatum D l hl L Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2
      |>.choose_spec.2.1
  have hdist := (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec
    |>.choose_spec.2.choose_spec.2.2
  refine ⟨fun T hT ↦ ?_⟩
  obtain ⟨T', hT', ⟨e⟩⟩ := (hdist T).1 hT
  exact Pretriangulated.isomorphic_distinguished _
    ((integralConstructibleScalarExtension D l hl E L ι Y ⋙
      rationalConstructibleLocalization D l hl L Y).map_distinguished T' hT') _
    ((rationalOrdinaryScalarExtension D l hl E Y L ι).mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso (rationalConstructibleLocalization D l hl E Y)
        (rationalOrdinaryScalarExtension D l hl E Y L ι)).symm.app T' ≪≫
      (Functor.mapTriangleIso (rationalOrdinaryLift D l hl E Y L ι)).app T')

/-- The published completed functor carries the unique shift comparison making its
normalized comparison with ordinary tensor commute with every integer shift.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: conjugate the ordinary derived tensor comparison by rationalOrdinaryComparison.
The ordinary comparison satisfies zero and addition coherence; naturality of the
conjugating isomorphism carries both equations to the completed functor. The displayed
commutation fixes every component uniquely, including the signed shift by one. -/
theorem rationalConstructibleScalarCommShift_existsUnique :
    ∃! c : (rationalScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst : (rationalScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        NatTrans.CommShift (rationalOrdinaryComparison D l hl E Y L ι).hom ℤ)
        (commInst := c) := by
  let e := rationalOrdinaryComparison D l hl E Y L ι
  refine existsUnique_of_exists_of_unique
    ⟨Functor.CommShift.ofIso e ℤ, Functor.CommShift.ofIso_compatibility e ℤ⟩ ?_
  intro c₁ c₂ h₁ h₂
  apply commShift_ext
  intro n K
  exact (commShiftIso_hom_app_of_natTrans (c := c₁) (h := h₁) e n K).trans
    (commShiftIso_hom_app_of_natTrans (c := c₂) (h := h₂) e n K).symm

/-- The shift comparison transported through the canonical completion comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalConstructibleScalarCommShift :
    (rationalScalarExtension D l hl E Y L ι).CommShift ℤ :=
  (rationalConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- The existing completed scalar functor is exact for its specified shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: ordinary finite free tensor is exact on sheaves and hence on derived complexes.
Restriction to the constructible full subcategories and rationalization preserve its
image triangles, proving rationalOrdinaryScalar_exact. The normalized natural
isomorphism rationalOrdinaryComparison commutes with the displayed shifts, so its
triangle isomorphisms transport preservation to the published completed functor. -/
theorem rationalConstructibleScalar_exact :
    (rationalScalarExtension D l hl E Y L ι).IsTriangulated := by
  have : NatTrans.CommShift (rationalOrdinaryComparison D l hl E Y L ι).hom ℤ :=
    (rationalConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose_spec
  have := rationalOrdinaryScalar_exact D l hl E Y L ι
  exact Functor.isTriangulated_of_iso (rationalOrdinaryComparison D l hl E Y L ι)

/-- The published scalar functor is additive by its original tensor-Hom specification.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalConstructibleScalar_additive :
    (rationalScalarExtension D l hl E Y L ι).Additive :=
  rationalScalarExtension_additive D l hl E Y L ι

attribute [instance] rationalConstructibleScalar_exact

end WeilConjectures
