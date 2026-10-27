/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.ScalarInverseImageIndependent
import all Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.RingTheory.Localization.Away.Basic
import all Sheaf.CategoryTheory.LocalizationInverseImageCoherence
import all Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses

/-! # Localization-normalized pullback and scalar tensor comparisons

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7E, 06YY, 0D6D;
sites-modules.tex, Section 03EK
(blueprint: lem-per-localized-pullback-tensor-normalization).

The localized inverse image is presented over the canonically identified ring R[1/t'].
Its ring identification is required to preserve the localization unit. All functors
below are the existing sheafified scalar extensions and their universal derived pairs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe uC vC uD vD r w
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.SuccessiveDerivedQuotient

namespace CategoryTheory.LocalizedPullbackTensor

section Coefficients
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]

/-- Select the existing universal derived coefficient-extension presentations. Their
ordinary objects and maps are fixed, and their derived pairs are determined up to the
unique universal comparison, rather than chosen from mere existence of arbitrary objects.
Source: Stacks 06YY, 0D6D (blueprint: lem-per-localized-pullback-tensor-normalization). -/
def presentation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    SheafOfModules.SuccessiveDerivedQuotient.Presentation a :=
  (Classical.choose (successive_derived_quotient_normalization (J := J))) a

/-- The existing tensor multiplication and insertion-of-one normalizations for these
presentations. This selects witnesses to the recorded normalization laws.
Source: Stacks 03EK, 0D6D (blueprint: lem-per-localized-pullback-tensor-normalization). -/
def normalization :
    SheafOfModules.SuccessiveDerivedQuotient.Normalization (presentation (J := J)) :=
  Classical.choice (Classical.choose_spec
    (successive_derived_quotient_normalization (J := J)))

/-- Flat-term K-flat is only an abbreviation for the two recorded predicates.
Source: Stacks 0G7E (blueprint: lem-per-localized-pullback-tensor-normalization). -/
abbrev FlatK {R : Sheaf J CommRingCat.{r}} (P : CochainComplex (Modules R) ℤ) : Prop :=
  P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P.X n)


attribute [local irreducible] presentation normalization
attribute [local irreducible] Functor.mapHomotopyCategoryCompIso
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

private def identityInverse (R : Sheaf J CommRingCat.{r}) :
    SheafOfModules.AlgebraicInverseImage (𝟭 (Sheaf J (Type r))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 (Modules R)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

private theorem scalarFlatK {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S)
    (T : CochainComplex (Modules R) ℤ) (hT : FlatK T) :
    FlatK (((presentation c).ordinary.mapHomologicalComplex (.up ℤ)).obj T) := by
  exact SheafOfModules.isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (identityInverse R) c (presentation c).ordinary (presentation c).obj_eq
    (presentation c).map_eq T hT.1 hT.2

end Coefficients

section Fractions
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- The actual sheafification image of r/t^m, including nilpotent denominators.
Source: Stacks 00CP, 03EK (blueprint: lem-per-localized-pullback-tensor-normalization). -/
def fraction (R : Sheaf J CommRingCat.{r})
    (t : (R.obj ⋙ forget CommRingCat.{r}).sections) (W : Cᵒᵖ)
    (a : R.obj.obj W) (m : ℕ) : (ringedLocalizationRingOfUniverses R t).obj.obj W :=
  ((toSheafify J (ringedLocalizationRingPresheafOfUniverses (C := C) (J := J) R t :
      Cᵒᵖ ⥤ CommRingCat.{r})).app W).hom
    (algebraMap (R.obj.obj W) (Localization.Away (M := R.obj.obj W) (t.val W)) a *
      (IsLocalization.Away.invSelf (R := R.obj.obj W)
        (S := Localization.Away (M := R.obj.obj W) (t.val W)) (t.val W)) ^ m)


private theorem localizationMap
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R S : Sheaf J CommRingCat.{r}) (c : R ⟶ S)
    (t : (R.obj ⋙ forget CommRingCat.{r}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{r}).sections)
    (hs : ∀ W : Cᵒᵖ, s.val W = (c.hom.app W).hom (t.val W)) :
    ∃ (e : ringedLocalizationRingOfUniverses R t ⟶ ringedLocalizationRingOfUniverses S s)
      (_he : ringedLocalizationRingUnitOfUniverses R t ≫ e =
        c ≫ ringedLocalizationRingUnitOfUniverses S s),
      ∀ (W : Cᵒᵖ) (a : R.obj.obj W) (m : ℕ),
        (e.hom.app W).hom (fraction R t W a m) =
          fraction S s W ((c.hom.app W).hom a) m := by
  let d := c ≫ ringedLocalizationRingUnitOfUniverses S s
  have hu (W : Cᵒᵖ) : IsUnit (d.hom.app W (t.val W)) := by
    change IsUnit ((ringedLocalizationRingUnitOfUniverses S s).hom.app W
      (c.hom.app W (t.val W)))
    rw [← hs W]
    exact LocalizationRings.unit_isUnit S s W
  let e := LocalizationRings.lift R t d hu
  have he := LocalizationRings.lift_unit R t d hu
  refine ⟨e, he, ?_⟩
  intro W a m
  let ηR := ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R t)).app W).hom
  let ηS := ((toSheafify J (ringedLocalizationRingPresheafOfUniverses S s)).app W).hom
  let f := (e.hom.app W).hom.comp ηR
  have hf (a : R.obj.obj W) :
      f (algebraMap _ (Localization.Away (M := R.obj.obj W) (t.val W)) a) =
        ηS (algebraMap _ (Localization.Away (M := S.obj.obj W) (s.val W)) (c.hom.app W a)) :=
    congrArg (fun k ↦ k.hom.app W a) he
  have hinv : f (IsLocalization.Away.invSelf (R := R.obj.obj W)
      (S := Localization.Away (M := R.obj.obj W) (t.val W))
      (t.val W)) =
      ηS (IsLocalization.Away.invSelf (R := S.obj.obj W)
      (S := Localization.Away (M := S.obj.obj W) (s.val W)) (s.val W)) := by
    have h₁ := congrArg f
      (IsLocalization.Away.mul_invSelf (R := R.obj.obj W)
        (S := Localization.Away (M := R.obj.obj W) (t.val W)) (t.val W))
    have h₂ := congrArg ηS
      (IsLocalization.Away.mul_invSelf (R := S.obj.obj W)
        (S := Localization.Away (M := S.obj.obj W) (s.val W)) (s.val W))
    rw [map_mul, map_one, hf, ← hs W] at h₁
    rw [map_mul, map_one] at h₂
    have hu' : IsUnit (ηS (algebraMap (S.obj.obj W)
        (Localization.Away (M := S.obj.obj W) (s.val W)) (s.val W))) := by
      exact (IsLocalization.Away.algebraMap_isUnit (R := S.obj.obj W)
        (S := Localization.Away (M := S.obj.obj W) (s.val W)) (s.val W)).map ηS
    exact hu'.mul_left_cancel (h₁.trans h₂.symm)
  change f (algebraMap _ (Localization.Away (M := R.obj.obj W) (t.val W)) a *
      IsLocalization.Away.invSelf (R := R.obj.obj W)
      (S := Localization.Away (M := R.obj.obj W) (t.val W)) (t.val W) ^ m) = _
  rw [map_mul, map_pow, hf, hinv]
  simp only [fraction, map_mul, map_pow]
  rfl

end Fractions

set_option backward.isDefEq.respectTransparency false



private theorem factorsAt
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} E]
    (F : A ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj T) =
      F.mapDerivedCategoryFactors.hom.app T := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app T ≫
    𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  erw [F.mapDerivedCategory.map_id (DerivedCategory.Q.obj T),
    DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ _).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj T))]
  simp only [Category.id_comp]
  exact Category.comp_id _

private theorem descendIso
    {A : Type*} {D₀ : Type*} {E : Type*}
    [Category A] [Category D₀] [Category E]
    (Q : A ⥤ D₀) (W : MorphismProperty A) [Q.IsLocalization W]
    (P : ObjectProperty A) [(P.ι ⋙ Q).IsLocalization (W.inverseImage P.ι)]
    (F G : D₀ ⥤ E) (F₀ G₀ : A ⥤ E)
    (εF : Q ⋙ F ⟶ F₀) (εG : Q ⋙ G ⟶ G₀)
    (hF : ∀ X, P X → IsIso (εF.app X))
    (hG : ∀ X, P X → IsIso (εG.app X)) (e : F₀ ≅ G₀) :
    ∃ d : F ≅ G, ∀ X, P X →
      d.hom.app (Q.obj X) ≫ εG.app X = εF.app X ≫ e.hom.app X := by
  let ε₁ := Functor.whiskerLeft P.ι εF
  let ε₂ := Functor.whiskerLeft P.ι εG
  have h₁ (X : P.FullSubcategory) : IsIso (ε₁.app X) := hF X.obj X.property
  have h₂ (X : P.FullSubcategory) : IsIso (ε₂.app X) := hG X.obj X.property
  have : IsIso ε₁ := NatIso.isIso_of_isIso_app ε₁
  have : IsIso ε₂ := NatIso.isIso_of_isIso_app ε₂
  let z : (P.ι ⋙ Q) ⋙ F ≅ (P.ι ⋙ Q) ⋙ G :=
    asIso ε₁ ≪≫ Functor.isoWhiskerLeft P.ι e ≪≫ (asIso ε₂).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft (P.ι ⋙ Q)
    (W.inverseImage P.ι) E
  let d : F ≅ G := ff.preimageIso z
  have hd : ((Functor.whiskeringLeft _ _ _).obj (P.ι ⋙ Q)).map d.hom = z.hom :=
    ff.map_preimage z.hom
  refine ⟨d, ?_⟩
  intro X hX
  have := hG X hX
  have hx := congrArg (fun q ↦ q.app (⟨X, hX⟩ : P.FullSubcategory)) hd
  dsimp only [z, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app] at hx
  change d.hom.app (Q.obj X) = εF.app X ≫ e.hom.app X ≫
    (asIso ε₂).inv.app ⟨X, hX⟩ at hx
  have := hG X hX
  rw [hx]
  change (εF.app X ≫ e.hom.app X ≫ (asIso ε₂).inv.app ⟨X, hX⟩) ≫
    (asIso ε₂).hom.app ⟨X, hX⟩ = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun f ↦ εF.app X ≫ f) (Category.comp_id (e.hom.app X))

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {J' : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J' AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}] [HasSheafify J' CommRingCat.{r}]
  [hDC : ∀ A : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules A)]
  [hDD : ∀ A : Sheaf J' CommRingCat.{r}, HasDerivedCategory.{w} (Modules A)]
  (L : Sheaf J (Type r) ⥤ Sheaf J' (Type r))
  (Lstar : Sheaf J' (Type r) ⥤ Sheaf J (Type r)) (adj : L ⊣ Lstar)
  [hL : PreservesFiniteLimits L]
  (B : Sheaf J CommRingCat.{r}) (R S : Sheaf J' CommRingCat.{r})
  (I : SheafOfModules.AlgebraicInverseImage L B R) (c : R ⟶ S)
  (t : (B.obj ⋙ forget CommRingCat.{r}).sections)
  (t' : (R.obj ⋙ forget CommRingCat.{r}).sections)
  (s : (S.obj ⋙ forget CommRingCat.{r}).sections)
  (ht : IsInverseImageSection I t t')
  (hs : ∀ W : Dᵒᵖ, s.val W = (c.hom.app W).hom (t'.val W))

/-- The unit-normalized algebraic presentation of inverse image after localization.
This is an equality of underlying ring-object maps; it excludes twisting the
localization identification by a ring automorphism.
Source: Stacks 00CP, 03EL (blueprint: lem-per-localized-pullback-tensor-normalization). -/
def UnitNormalized
    (It : SheafOfModules.AlgebraicInverseImage L (ringedLocalizationRingOfUniverses B t)
      (ringedLocalizationRingOfUniverses R t')) : Prop :=
  L.map ((sheafCompose J (forget CommRingCat.{r})).map
      (ringedLocalizationRingUnitOfUniverses B t)) ≫ It.ringUnderlying.hom =
    I.ringUnderlying.hom ≫ (sheafCompose J' (forget CommRingCat.{r})).map
      (ringedLocalizationRingUnitOfUniverses R t')

variable (It : SheafOfModules.AlgebraicInverseImage L (ringedLocalizationRingOfUniverses B t)
    (ringedLocalizationRingOfUniverses R t'))
  (hIt : UnitNormalized L B R I t t' It)
  [I.modules.Additive] [PreservesFiniteLimits I.modules] [PreservesFiniteColimits I.modules]
  [It.modules.Additive] [PreservesFiniteLimits It.modules] [PreservesFiniteColimits It.modules]


set_option linter.unusedSectionVars false in
include Lstar adj in
private theorem inverseFlatK (T : CochainComplex (Modules B) ℤ) (hT : FlatK T) :
    FlatK ((I.modules.mapHomologicalComplex (.up ℤ)).obj T) := by
  refine ⟨SheafOfModules.kFlat_inverseImage_independent L Lstar adj I T hT.1 hT.2, ?_⟩
  intro n
  exact SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{uC, vC, uD, vD, r, r}
    L Lstar adj
    (SheafOfModules.inverseImageOfUniverses I) (T.X n) (hT.2 n)

attribute [local irreducible] ringedLocalizationRingOfUniverses
attribute [local irreducible] ringedLocalizationRingUnitOfUniverses

include Lstar adj hIt in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 200000 in
-- The generalized-element comparison elaborates both scalar-extension adjunction units.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryGamma :
    ∃ gamma : (presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary ⋙
        It.modules ≅ I.modules ⋙
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')).ordinary,
      ∀ (M : Modules B) (T : Sheaf J (Type r))
        (v : T ⟶ (sheafCompose J (forget CommRingCat.{r})).obj
          (ringedLocalizationRingOfUniverses B t))
        (x : T ⟶ (localizationModuleSets B).obj M)
        (y : T ⟶ (localizationModuleSets (ringedLocalizationRingOfUniverses B t)).obj
          ((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary.obj M)),
        (∀ (W : Cᵒᵖ) (z : T.obj.obj W), y.hom.app W z =
          sectionTensor (presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)) M W
            (v.hom.app W z) (x.hom.app W z)) →
        ∀ (W : Dᵒᵖ) (z : (L.obj T).obj.obj W),
          ((gamma.hom.app M).val.app W)
            ((It.moduleUnderlying.inv.app _).hom.app W ((L.map y).hom.app W z)) =
          sectionTensor (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t'))
            (I.modules.obj M) W (It.ringUnderlying.hom.hom.app W ((L.map v).hom.app W z))
            ((I.moduleUnderlying.inv.app M).hom.app W ((L.map x).hom.app W z)) := by
  classical
  let jB := ringedLocalizationRingUnitOfUniverses B t
  let jR := ringedLocalizationRingUnitOfUniverses R t'
  let nB := normalization (J := J) (hD := hDC)
  let nR := normalization (J := J') (hD := hDD)
  obtain ⟨gamma, hu⟩ :=
    SheafOfModules.ScalarIndependent.exists_scalarInverseImageIndependent L Lstar adj I It
      jB jR hIt (presentation (hD := hDC) jB).ordinary (presentation (hD := hDD) jR).ordinary
      (nB.ordinaryAdjunction jB) (nR.ordinaryAdjunction jR)
  refine ⟨gamma, ?_⟩
  intro M T v x y hy W z
  let uB := (localizationModuleSets B).map ((nB.ordinaryAdjunction jB).unit.app M)
  let uR := (localizationModuleSets R).map
    ((nR.ordinaryAdjunction jR).unit.app (I.modules.obj M))
  have hp := It.moduleSMul ((presentation (hD := hDC) jB).ordinary.obj M) T v (x ≫ uB) y
    (by
      intro U q
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      exact (hy U q).trans
        ((sectionTensor_smul_one (presentation (hD := hDC) jB) M U _ _).trans
          (congrArg (fun (a :
              ((presentation (hD := hDC) jB).ordinary.obj M).val.obj U) ↦
              (v.hom.app U q : (ringedLocalizationRingOfUniverses B t).obj.obj U) • a)
            (nB.ordinary_unit jB M U (x.hom.app U q)).symm))) W z
  have hm : ((L.map (x ≫ uB) ≫ It.moduleUnderlying.inv.app _) ≫
      (localizationModuleSets (ringedLocalizationRingOfUniverses R t')).map
        (gamma.hom.app M)) =
      (L.map x ≫ I.moduleUnderlying.inv.app M) ≫ uR := by
    rw [L.map_comp]
    have hunit := congrArg (fun f ↦ L.map x ≫ f) (hu M)
    dsimp only [uB, uR]
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [Category.assoc] using hunit
  have hm' := congrArg (fun f ↦ f.hom.app W z) hm
  dsimp only [uR] at hm'
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact (congrArg (fun (a : (It.modules.obj
      ((presentation (hD := hDC) jB).ordinary.obj M)).val.obj W) ↦
      (gamma.hom.app M).val.app W a) hp).trans
    ((((gamma.hom.app M).val.app W).hom.map_smul _ _).trans
      ((congrArg (fun (a :
          ((presentation (hD := hDD) jR).ordinary.obj (I.modules.obj M)).val.obj W) ↦
          It.ringUnderlying.hom.hom.app W ((L.map v).hom.app W z) • a) hm').trans
        ((congrArg (fun (a :
            ((presentation (hD := hDD) jR).ordinary.obj (I.modules.obj M)).val.obj W) ↦
            It.ringUnderlying.hom.hom.app W ((L.map v).hom.app W z) • a)
          (nR.ordinary_unit jR (I.modules.obj M) W
            ((I.moduleUnderlying.inv.app M).hom.app W ((L.map x).hom.app W z)))).trans
          (sectionTensor_smul_one (presentation (hD := hDD) jR)
            (I.modules.obj M) W _ _).symm)))



include Lstar adj in
set_option Elab.async false in
set_option maxHeartbeats 250000 in
-- The comparison equations retain all dependent computation maps.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derivedSquare
    (gamma : (presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary ⋙
      It.modules ≅ I.modules ⋙
        (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')).ordinary) :
    ∃ d : (presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).derived ⋙
        It.modules.mapDerivedCategory ≅ I.modules.mapDerivedCategory ⋙
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')).derived,
      ∀ T : CochainComplex (Modules B) ℤ, FlatK T →
        d.hom.app (DerivedCategory.Q.obj T) ≫
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')).derived.map
            (I.modules.mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient _ _).obj T)) ≫
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')).counit.app
            ((I.modules.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj T)) =
        It.modules.mapDerivedCategory.map
          ((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).counit.app
            ((HomotopyCategory.quotient _ _).obj T)) ≫
        It.modules.mapDerivedCategoryFactorsh.hom.app
          ((((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary
            ).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj T)) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso gamma (.up ℤ)).hom.app
            ((HomotopyCategory.quotient _ _).obj T)) := by
  let P : ObjectProperty (HomotopyCategory (Modules B) (.up ℤ)) := fun X ↦ FlatK X.as
  let W := HomotopyCategory.quasiIso (Modules B) (.up ℤ)
  have hloc : (P.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage P.ι) := by
    apply SheafOfModules.restriction_localization W DerivedCategory.Qh P
    intro X
    obtain ⟨K, f, hK, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    have hs' (n : ℤ) : SheafOfModules.IsFlatOnSite (K.X n) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso B (K.X n)).symm (hflat n)
    refine ⟨⟨(HomotopyCategory.quotient _ _).obj K, hK, hs'⟩,
      (HomotopyCategory.quotient _ _).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  let EB := presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)
  let ER := presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')
  let εF : DerivedCategory.Qh ⋙ (EB.derived ⋙ It.modules.mapDerivedCategory) ⟶
      (EB.ordinary.mapHomotopyCategory (.up ℤ) ⋙
        It.modules.mapHomotopyCategory (.up ℤ)) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight EB.counit It.modules.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (EB.ordinary.mapHomotopyCategory (.up ℤ))
        It.modules.mapDerivedCategoryFactorsh.hom ≫ (Functor.associator _ _ _).inv
  let εG : DerivedCategory.Qh ⋙ (I.modules.mapDerivedCategory ⋙ ER.derived) ⟶
      (I.modules ⋙ ER.ordinary).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight I.modules.mapDerivedCategoryFactorsh.hom ER.derived ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (I.modules.mapHomotopyCategory (.up ℤ)) ER.counit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (I.modules ⋙ ER.ordinary))
          (.up ℤ)).hom DerivedCategory.Qh
  have hF X (hX : P X) : IsIso (εF.app X) := by
    have : IsIso (EB.counit.app X) :=
      (normalization (J := J) (hD := hDC)).computed _ X.as hX.1 hX.2
    dsimp only [εF, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hG X (hX : P X) : IsIso (εG.app X) := by
    have hI := inverseFlatK L Lstar adj B R I X.as hX
    have : IsIso (ER.counit.app ((I.modules.mapHomotopyCategory (.up ℤ)).obj X)) :=
      (normalization (J := J') (hD := hDD)).computed _ _ hI.1 hI.2
    dsimp only [εG, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨d, hd⟩ := descendIso DerivedCategory.Qh W P _ _ _ _ εF εG hF hG
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso gamma (.up ℤ))
      DerivedCategory.Qh)
  refine ⟨d, ?_⟩
  intro T hT
  have h := hd ((HomotopyCategory.quotient _ _).obj T) hT
  have hc := Functor.mapHomotopyCategoryCompIso_refl_hom_app (.up ℤ)
    I.modules ER.ordinary ((HomotopyCategory.quotient _ _).obj T)
  dsimp only [εF, εG, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at h
  simp only [
    Category.id_comp, Category.comp_id, Category.assoc] at h
  erw [hc, DerivedCategory.Qh.map_id, Category.comp_id] at h
  exact h




private theorem imageQuotientObj {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive]
    (T : CochainComplex A ℤ) :
    (F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient A (.up ℤ)).obj T) =
      (HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj T) := rfl

private theorem imageCompObj {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (T : CochainComplex A ℤ) :
    ((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj T =
      (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T) := rfl

private theorem quotientDerivedObj {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory.{w} A] (T : CochainComplex A ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj T) =
      DerivedCategory.Q.obj T := rfl

private theorem towerComputation {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C} (e : F ⋙ G ≅ H)
    {X Y : A} {Z : B} {W V : C} (f : X ⟶ Y) (u : F.obj Y ⟶ Z)
    (v : G.obj Z ⟶ W) (z : W ⟶ V) (ε : H.obj Y ⟶ V)
    (hr : e.hom.app Y ≫ ε = G.map u ≫ v ≫ z) :
    e.hom.app X ≫ H.map f ≫ ε = G.map (F.map f ≫ u) ≫ v ≫ z := by
  rw [← Category.assoc, ← e.hom.naturality f, Category.assoc, hr]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]


private theorem composeComputation {A B : Type*} [Category A] [Category B]
    (E : A ⥤ B) {X Y Z V W : A} {Y' Z' P Q H : B}
    (q : X ⟶ Y) (f : Y ⟶ Z) (ε : Z ⟶ W) (u : X ⟶ V) (v : V ⟶ W)
    (rY : E.obj Y ⟶ Y') (rZ : E.obj Z ⟶ Z') (g : Y' ⟶ Z') (h : Z' ⟶ H)
    (εW : E.obj W ⟶ P) (εV : E.obj V ⟶ Q) (v' : Q ⟶ P) (z : P ⟶ H)
    (hn : rY ≫ g = E.map f ≫ rZ) (hr : rZ ≫ h = E.map ε ≫ εW ≫ z)
    (hq : q ≫ f ≫ ε = u ≫ v) (hε : E.map v ≫ εW = εV ≫ v') :
    (E.map q ≫ rY) ≫ g ≫ h = E.map u ≫ εV ≫ v' ≫ z := by
  calc
    _ = E.map (q ≫ f ≫ ε) ≫ εW ≫ z := by
      rw [Category.assoc, ← Category.assoc rY, hn]
      simp only [Category.assoc]
      rw [hr]
      simp only [Functor.map_comp, Category.assoc]
    _ = E.map (u ≫ v) ≫ εW ≫ z := by rw [hq]
    _ = _ := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
      rw [← Category.assoc (E.map v), hε]
      simp only [Category.assoc]


private theorem transportCounit {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {X : Type*} (Q : A ⥤ B) (Q' : C ⥤ D) (E : X → B ⥤ D) (G : X → A ⥤ C)
    (ε : ∀ x, Q ⋙ E x ⟶ G x ⋙ Q') {x y : X} (h : x = y)
    {V : B} {W : A} (f : V ⟶ Q.obj W) :
    (eqToIso (congrArg E h)).hom.app V ≫ (E y).map f ≫ (ε y).app W =
      (E x).map f ≫ (ε x).app W ≫
        eqToHom (congrArg (fun z ↦ Q'.obj ((G z).obj W)) h) := by
  cases h
  simp


private theorem transportComputation {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {X : Type*} (Q : A ⥤ B) (Q' : C ⥤ D) (E : X → B ⥤ D) (G : X → A ⥤ C)
    (ε : ∀ x, Q ⋙ E x ⟶ G x ⋙ Q') {x y : X} (h : x = y)
    {V : B} {W : A} (f : V ⟶ Q.obj W) {Z : D} (q : Z ⟶ (E x).obj V)
    (r : Z ⟶ Q'.obj ((G x).obj W))
    (hr : q ≫ (E x).map f ≫ (ε x).app W = r) :
    (q ≫ (eqToIso (congrArg E h)).hom.app V) ≫ (E y).map f ≫ (ε y).app W =
      r ≫ eqToHom (congrArg (fun z ↦ Q'.obj ((G z).obj W)) h) := by
  cases h
  simpa using hr


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

include adj ht hs hIt hL

set_option linter.unusedSectionVars false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- The large dependent conclusion needs extra elaboration heartbeats.
/-- The full pair of localized pullback comparisons, with ordinary tensor formulas,
canonical derived computation, preservation of the resolving class, and naturality on
all derived morphisms. `It` is g^{-1} on V-modules after the canonical unit-preserving
identification g^{-1}V = R_t, not a replacement for geometric inverse image.
The exactness instances on I and It are the forced exactness of algebraic inverse image
(`localization_inverseImage_exact`), not flatness assumptions on c.

Source: Stacks 06YS, 0G7E, 06YY, 0D6D and Section 03EK
(blueprint: lem-per-localized-pullback-tensor-normalization).

Proof, following the seven DAG steps:
1. Resolve K by a flat-term K-flat T using lem-pc-kflat-resolution. Apply
lem-weil-pbc-ringed-topos-kflat-pullback to inverse image and to each scalar extension,
including B to V. This proves every flatness and K-flatness assertion below.
2. The composite R to S to U inverts t'. The sectionwise localization universal
property supplies e, r/(t')^m mapped to c(r)s^{-m}; uniqueness glues restrictions and
sheafification. If (t')^k((t')^n r-(t')^m r')=0, apply c and divide by s^{k+m+n}.
Thus the fraction formula is valid even with zero divisors or zero localization.
3. The sheaf tensor bilinear universal property constructs the first flattening,
u tensor (v tensor n) mapped to u v tensor n. Its inverse inserts one. Inner R and
outer S balancing hold by multiplicativity of c and the scalar action.
4. The second flattening multiplies u by e(q), with inverse inserting one. Inner R
balancing uses e(r/1)=c(r); outer R_t balancing uses e(aq)=e(a)e(q). Both composites
are identities by moving the middle scalar across the outer tensor.
5. The localization inverse-image coherence lemma identifies the pulled-back
localized complex with R_t tensor N. Its generalized pure-tensor formula is gamma
below; its ring normalization is hIt. The canonical derived computation counits of
lem-weil-pbc-ringed-topoi-derived-pullback compute all three displayed derived objects.
The two representative equations identify their comparisons with the chain flattenings.
6. Coefficients have degree zero: both routes through the differential give u v tensor
dn, respectively u e(q) tensor dn. The same formulas commute with chain maps and degree
minus one homotopies. The ordinary comparisons therefore induce the homotopy maps below.
7. Apply the resolving-class localization equivalence of site-derived-tensor-descent
and the natural-transformation universal property of localization. The comparisons
descend to natural isomorphisms a and b. Uniqueness proves independence of all flat-term
K-flat resolutions; naturality includes inverted quasi-isomorphisms and every derived map.
-/
theorem localizedPullbackTensorNormalization :
    ∃ (e : ringedLocalizationRingOfUniverses R t' ⟶ ringedLocalizationRingOfUniverses S s)
      (he : ringedLocalizationRingUnitOfUniverses R t' ≫ e =
        c ≫ ringedLocalizationRingUnitOfUniverses S s),
      (∀ (W : Dᵒᵖ) (r₀ : R.obj.obj W) (m : ℕ),
        (e.hom.app W).hom (fraction R t' W r₀ m) =
          fraction S s W ((c.hom.app W).hom r₀) m) ∧
    ∃ gamma : (presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary ⋙
        It.modules ≅ I.modules ⋙
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')).ordinary,
    ∃ a : (I.modules.mapDerivedCategory ⋙ (presentation (hD := hDD) c).derived) ⋙
        (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses S s)).derived ≅
      I.modules.mapDerivedCategory ⋙
        (presentation (hD := hDD) (c ≫ ringedLocalizationRingUnitOfUniverses S s)).derived,
    ∃ b : ((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).derived ⋙
        It.modules.mapDerivedCategory) ⋙ (presentation (hD := hDD) e).derived ≅
      I.modules.mapDerivedCategory ⋙
        (presentation (hD := hDD) (c ≫ ringedLocalizationRingUnitOfUniverses S s)).derived,
      (∀ (M : Modules B) (T : Sheaf J (Type r))
        (v : T ⟶ (sheafCompose J (forget CommRingCat.{r})).obj
          (ringedLocalizationRingOfUniverses B t))
        (x : T ⟶ (localizationModuleSets B).obj M)
        (y : T ⟶ (localizationModuleSets (ringedLocalizationRingOfUniverses B t)).obj
          ((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary.obj M)),
        (∀ (W : Cᵒᵖ) (z : T.obj.obj W), y.hom.app W z =
          sectionTensor (presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)) M W
            (v.hom.app W z) (x.hom.app W z)) →
        ∀ (W : Dᵒᵖ) (z : (L.obj T).obj.obj W),
          ((gamma.hom.app M).val.app W)
            ((It.moduleUnderlying.inv.app _).hom.app W ((L.map y).hom.app W z)) =
          sectionTensor (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t'))
            (I.modules.obj M) W (It.ringUnderlying.hom.hom.app W ((L.map v).hom.app W z))
            ((I.moduleUnderlying.inv.app M).hom.app W ((L.map x).hom.app W z))) ∧
      (∀ T : CochainComplex (Modules B) ℤ, FlatK T →
        FlatK (((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary
          ).mapHomologicalComplex (.up ℤ) |>.obj T) ∧
        FlatK ((I.modules.mapHomologicalComplex (.up ℤ)).obj T) ∧
        FlatK (((I.modules ⋙ (presentation (hD := hDD) c).ordinary
          ).mapHomologicalComplex (.up ℤ)).obj T) ∧
        FlatK (((I.modules ⋙
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')).ordinary
            ).mapHomologicalComplex (.up ℤ)).obj T) ∧
        FlatK (((I.modules ⋙
          (presentation (hD := hDD) (c ≫ ringedLocalizationRingUnitOfUniverses S s)).ordinary
            ).mapHomologicalComplex (.up ℤ)).obj T) ∧
        FlatK ((((I.modules ⋙ (presentation (hD := hDD) c).ordinary) ⋙
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses S s)).ordinary
            ).mapHomologicalComplex (.up ℤ)).obj T) ∧
        FlatK ((((I.modules ⋙
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses R t')).ordinary) ⋙
            (presentation (hD := hDD) e).ordinary).mapHomologicalComplex (.up ℤ)).obj T) ∧
        FlatK ((((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary ⋙
          It.modules).mapHomologicalComplex (.up ℤ)).obj T)) ∧
      (∀ T : CochainComplex (Modules B) ℤ, FlatK T →
        a.hom.app (DerivedCategory.Q.obj T) ≫
            (presentation (hD := hDD) (c ≫ ringedLocalizationRingUnitOfUniverses S s)).derived.map
              (I.modules.mapDerivedCategoryFactors.hom.app T) ≫
            (presentation (hD := hDD) (c ≫ ringedLocalizationRingUnitOfUniverses S s)).counit.app
              ((I.modules.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient _ _).obj T)) =
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses S s)).derived.map
            ((presentation (hD := hDD) c).derived.map
              (I.modules.mapDerivedCategoryFactors.hom.app T) ≫
              (presentation (hD := hDD) c).counit.app ((I.modules.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient _ _).obj T))) ≫
          (presentation (hD := hDD) (ringedLocalizationRingUnitOfUniverses S s)).counit.app
            (((I.modules.mapHomotopyCategory (.up ℤ)) ⋙
              (presentation (hD := hDD) c).ordinary.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient _ _).obj T)) ≫
          (DerivedCategory.Qh (C := Modules
              (ringedLocalizationRingOfUniverses S s))).map
            ((Functor.mapHomotopyCategoryCompIso
              ((normalization (J := J') (hD := hDD)).ordinary c
                (ringedLocalizationRingUnitOfUniverses S s)) (.up ℤ)).hom.app
                  ((I.modules.mapHomotopyCategory (.up ℤ)).obj
                    ((HomotopyCategory.quotient _ _).obj T)))) ∧
      (∀ T : CochainComplex (Modules B) ℤ, FlatK T →
        b.hom.app (DerivedCategory.Q.obj T) ≫
            (presentation (hD := hDD) (c ≫ ringedLocalizationRingUnitOfUniverses S s)).derived.map
              (I.modules.mapDerivedCategoryFactors.hom.app T) ≫
            (presentation (hD := hDD) (c ≫ ringedLocalizationRingUnitOfUniverses S s)).counit.app
              ((I.modules.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient _ _).obj T)) =
          (presentation (hD := hDD) e).derived.map
            (It.modules.mapDerivedCategory.map
              ((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).counit.app
                ((HomotopyCategory.quotient _ _).obj T)) ≫
              It.modules.mapDerivedCategoryFactorsh.hom.app
                ((((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary
                  ).mapHomotopyCategory (.up ℤ)).obj
                    ((HomotopyCategory.quotient _ _).obj T))) ≫
          (presentation (hD := hDD) e).counit.app
            ((((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary
              ).mapHomotopyCategory (.up ℤ) ⋙ It.modules.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient _ _).obj T)) ≫
          (DerivedCategory.Qh (C := Modules
              (ringedLocalizationRingOfUniverses S s))).map
            ((presentation (hD := hDD) e).ordinary.mapHomotopyCategory (.up ℤ) |>.map
              ((Functor.mapHomotopyCategoryCompIso gamma (.up ℤ)).hom.app
                ((HomotopyCategory.quotient _ _).obj T))) ≫
          (DerivedCategory.Qh (C := Modules
              (ringedLocalizationRingOfUniverses S s))).map
            ((Functor.mapHomotopyCategoryCompIso
              ((normalization (J := J') (hD := hDD)).ordinary
                (ringedLocalizationRingUnitOfUniverses R t') e) (.up ℤ)).hom.app
                  ((I.modules.mapHomotopyCategory (.up ℤ)).obj
                    ((HomotopyCategory.quotient _ _).obj T))) ≫
          eqToHom (congrArg (fun (f : R ⟶ ringedLocalizationRingOfUniverses S s) ↦
            (DerivedCategory.Qh (C := Modules (ringedLocalizationRingOfUniverses S s))).obj
            (((presentation (hD := hDD) f).ordinary.mapHomotopyCategory (.up ℤ)).obj
              ((I.modules.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient _ _).obj T))))
            he)) := by
  classical
  have hmap := localizationMap (C := D) (J := J') R S c t' s hs
  obtain ⟨e, he, hfrac⟩ := hmap
  obtain ⟨gamma, hgamma⟩ := ordinaryGamma L Lstar adj B R I t t' It hIt
  let jS := ringedLocalizationRingUnitOfUniverses S s
  let nS := normalization (J := J') (hD := hDD)
  let a := Functor.associator I.modules.mapDerivedCategory
    (presentation c).derived (presentation jS).derived ≪≫
      Functor.isoWhiskerLeft I.modules.mapDerivedCategory (nS.derived c jS)
  refine ⟨e, he, hfrac, gamma, a, ?_⟩
  obtain ⟨q, hq⟩ := derivedSquare L Lstar adj B R I t t' It gamma
  let j := ringedLocalizationRingUnitOfUniverses R t'
  let n := normalization (J := J') (hD := hDD)
  let b0 := Functor.isoWhiskerRight q (presentation (hD := hDD) e).derived ≪≫
    Functor.associator I.modules.mapDerivedCategory (presentation (hD := hDD) j).derived
      (presentation (hD := hDD) e).derived ≪≫
    Functor.isoWhiskerLeft I.modules.mapDerivedCategory (n.derived j e)
  let b := b0 ≪≫ Functor.isoWhiskerLeft I.modules.mapDerivedCategory
      (eqToIso (congrArg (fun f ↦ (presentation (hD := hDD) f).derived) he))
  refine ⟨b, hgamma, ?_, ?_, ?_⟩
  · intro T hT
    let N := (I.modules.mapHomologicalComplex (.up ℤ)).obj T
    have hI := inverseFlatK L Lstar adj B R I T hT
    have hB := scalarFlatK (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t) T hT
    have hc := scalarFlatK (hD := hDD) c N hI
    have hR := scalarFlatK (hD := hDD) j N hI
    refine ⟨hB, hI, hc, hR, ?_, ?_, ?_, ?_⟩
    · exact scalarFlatK (hD := hDD) (c ≫ jS) N hI
    · exact scalarFlatK (hD := hDD) jS
        (((presentation (hD := hDD) c).ordinary.mapHomologicalComplex (.up ℤ)).obj N) hc
    · exact scalarFlatK (hD := hDD) e
        (((presentation (hD := hDD) j).ordinary.mapHomologicalComplex (.up ℤ)).obj N) hR
    · exact inverseFlatK L Lstar adj (ringedLocalizationRingOfUniverses B t)
        (ringedLocalizationRingOfUniverses R t') It
        (((presentation (hD := hDC)
          (ringedLocalizationRingUnitOfUniverses B t)).ordinary.mapHomologicalComplex
            (.up ℤ)).obj T) hB
  · intro T hT
    set_option backward.isDefEq.respectTransparency false in
    have hI := inverseFlatK L Lstar adj B R I T hT
    have hr := nS.representative c jS
      ((I.modules.mapHomologicalComplex (.up ℤ)).obj T) hI.1 hI.2
    dsimp only [a, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, NatTrans.comp_app, Functor.associator_hom_app]
    erw [Category.id_comp]
    have h := towerComputation (nS.derived c jS)
      (I.modules.mapDerivedCategoryFactors.hom.app T) _ _ _ _ hr
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact h
  · intro T hT
    have hb0 : b0.hom.app (DerivedCategory.Q.obj T) ≫
        (presentation (hD := hDD) (j ≫ e)).derived.map
          (I.modules.mapDerivedCategoryFactors.hom.app T) ≫
        (presentation (hD := hDD) (j ≫ e)).counit.app
          ((I.modules.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T)) =
      (presentation (hD := hDD) e).derived.map
            (It.modules.mapDerivedCategory.map
              ((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).counit.app
                ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T)) ≫
              It.modules.mapDerivedCategoryFactorsh.hom.app
                ((((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary
                  ).mapHomotopyCategory (.up ℤ)).obj
                    ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T))) ≫
          (presentation (hD := hDD) e).counit.app
            ((((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary
              ).mapHomotopyCategory (.up ℤ) ⋙ It.modules.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T)) ≫
          DerivedCategory.Qh.map
            ((presentation (hD := hDD) e).ordinary.mapHomotopyCategory (.up ℤ) |>.map
              ((Functor.mapHomotopyCategoryCompIso gamma (.up ℤ)).hom.app
                ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T))) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso
              ((normalization (J := J') (hD := hDD)).ordinary
                (ringedLocalizationRingUnitOfUniverses R t') e) (.up ℤ)).hom.app
                  ((I.modules.mapHomotopyCategory (.up ℤ)).obj
                    ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T))) := by
      have hI := inverseFlatK L Lstar adj B R I T hT
      have hr := n.representative j e
        ((I.modules.mapHomologicalComplex (.up ℤ)).obj T) hI.1 hI.2
      have hn := (n.derived j e).hom.naturality
        (I.modules.mapDerivedCategoryFactors.hom.app T)
      have hq' := hq T hT
      simp only [imageQuotientObj] at hq' 
      have hε := (presentation (hD := hDD) e).counit.naturality
        ((Functor.mapHomotopyCategoryCompIso gamma (.up ℤ)).hom.app
          ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T))
      dsimp only [Functor.comp_map] at hε
      simp only [Functor.comp_obj, imageQuotientObj, imageCompObj] at hε
      dsimp only [b0, Iso.trans_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        NatTrans.comp_app, Functor.associator_hom_app]
      erw [Category.id_comp]
      change ((presentation (hD := hDD) e).derived.map (q.hom.app (DerivedCategory.Q.obj T)) ≫
        (n.derived j e).hom.app (I.modules.mapDerivedCategory.obj
          (DerivedCategory.Q.obj T))) ≫ _ = _
      dsimp only [Functor.comp_map] at hn
      erw [factorsAt I.modules T] at hq'
      let ξ := DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso gamma (.up ℤ)).hom.app
          ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T))
      let u := It.modules.mapDerivedCategory.map
        ((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).counit.app
          ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T)) ≫
        It.modules.mapDerivedCategoryFactorsh.hom.app
          (((presentation (hD := hDC) (ringedLocalizationRingUnitOfUniverses B t)).ordinary
            ).mapHomotopyCategory (.up ℤ) |>.obj
              ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T))
      have h := composeComputation (presentation (hD := hDD) e).derived
        (q.hom.app (DerivedCategory.Q.obj T))
        ((presentation (hD := hDD) j).derived.map
          (I.modules.mapDerivedCategoryFactors.hom.app T))
        ((presentation (hD := hDD) j).counit.app
          ((I.modules.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient (Modules B) (.up ℤ)).obj T))) u ξ
        _ _ _ _ _ _ _ _ hn.symm hr
        (by
          dsimp only [u, ξ]
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            simpa only [j, Category.assoc, imageQuotientObj] using hq')
        (by simpa only [j, ξ, Functor.comp_obj, Functor.comp_map, imageQuotientObj,
          imageCompObj] using hε)
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        simpa only [u, ξ, j, n, Category.assoc, Functor.comp_obj, Functor.comp_map,
          imageQuotientObj, quotientDerivedObj] using h
    dsimp only [b, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, NatTrans.comp_app]
    have h := transportComputation DerivedCategory.Qh DerivedCategory.Qh
      (fun f ↦ (presentation (hD := hDD) f).derived)
      (fun f ↦ (presentation (hD := hDD) f).ordinary.mapHomotopyCategory (.up ℤ))
      (fun f ↦ (presentation (hD := hDD) f).counit) he
      (I.modules.mapDerivedCategoryFactors.hom.app T)
      (b0.hom.app (DerivedCategory.Q.obj T)) _ hb0
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      set_option backward.defeqAttrib.useBackward true in
      simpa only [j, Category.assoc, Functor.comp_obj, imageQuotientObj,
        Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient,
        CategoryTheory.Quotient.functor] using h

end CategoryTheory.LocalizedPullbackTensor
