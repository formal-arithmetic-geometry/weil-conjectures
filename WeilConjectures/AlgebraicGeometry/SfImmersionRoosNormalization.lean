/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparisonSupplement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.ExactAdjointTowerModels
import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.CompletedOpenExchangeTransport
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Uniqueness and normalization of the strict Roos comparison

Source: localization Step 6, the strict Roos model of derived inverse limit.
The comparison is determined on K-injectives and extended by naturality along
functorial K-injective resolutions. The remaining private helpers transport the
existing exact-products comparison to the positive-difference convention.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
attribute [local irreducible] CategoryTheory.Limits.limit HasDerivedCategory.standard

universe u uA vA w

/-- Naturality and equality on K-injectives determine the Roos comparison.

Source: localization Step 6, strict Roos/derived-limit normalization.
For a complex M, choose its functorial K-injective resolution q : M → I.
Localization sends q to an isomorphism, so its image under derived inverse
limit is invertible. Postcompose both comparisons with this image. Their
naturality squares identify the composites with the Roos image of q followed
by the comparisons on I. These agree by hypothesis. Cancel the invertible
postcomposition. This also covers zero complexes and zero categories.
(blueprint: lem-sf-roos-comparison-resolution-uniqueness) -/
theorem sfRoosComparison_ext
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    (e e' : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.{w}.obj (strictRoosComplex M) ≅
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.obj (DerivedCategory.Q.{w}.obj M))
    (he : ∀ (M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a : M ⟶ N),
      DerivedCategory.Q.{w}.map (roosF.map a) ≫ (e N).hom =
        (e M).hom ≫ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.map
          (DerivedCategory.Q.{w}.map a))
    (he' : ∀ (M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a : M ⟶ N),
      DerivedCategory.Q.{w}.map (roosF.map a) ≫ (e' N).hom =
        (e' M).hom ≫ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.map
          (DerivedCategory.Q.{w}.map a))
    (hI : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective], e I = e' I) :
    e = e' := by
  funext M
  apply Iso.ext
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} (ℕᵒᵖ ⥤ A)).obj M
  have : I.IsKInjective := by
    dsimp only [I]
    infer_instance
  let q : M ⟶ I := (CochainComplex.toKInjectiveResolution.{u} (ℕᵒᵖ ⥤ A)).app M
  have : QuasiIso q :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} (ℕᵒᵖ ⥤ A) M).2
  apply (cancel_mono ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.map
    (DerivedCategory.Q.{w}.map q))).mp
  exact (he M I q).symm.trans ((congrArg
    (fun z ↦ DerivedCategory.Q.{w}.map (roosF.map q) ≫ z)
    (congrArg Iso.hom (hI I))).trans (he' M I q))

private theorem normalized_roos_iso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    [HasExactLimitsOfShape (Discrete ℕ) A] :
    ∃ e : roosF (A := A) ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor,
      ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        DerivedCategory.Q.{w}.map (roosι M) ≫ e.hom.app M =
          DerivedCategory.Q.{w}.map (ExactAdjointTowerModels.ordinaryIso.inv.app M) ≫
            (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ M := by
  let F : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let η : ExactProductsRoos.ordinary ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun _ _ a ↦ F.rightDerivedFunctorUnitQ_naturality a }
  obtain ⟨β, hβ⟩ := ExactProductsRoos.comparisonIso F.rightDerivedFunctor η
    (fun I hI ↦ by
      let := hI
      change IsIso (F.rightDerivedFunctorUnitQ I)
      rw [F.rightDerivedFunctorUnitQ_eq]
      infer_instance)
  let σ := ExactAdjointTowerModels.signIso (A := A)
  let o := ExactAdjointTowerModels.ordinaryIso (A := A)
  let e := isoWhiskerRight σ.symm DerivedCategory.Q.{w} ≪≫ β
  refine ⟨e, fun M ↦ ?_⟩
  have hs : roosι M ≫ σ.inv.app M = o.inv.app M ≫ ExactProductsRoos.comparison.app M := by
    apply (cancel_mono (σ.hom.app M)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    have h := congr_app (ExactAdjointTowerModels.inclusion_sign (A := A)) M
    have h' := congrArg (fun z ↦ o.inv.app M ≫ z) h
    simpa only [NatTrans.comp_app, o, σ, roosInclusion, Category.assoc,
      Iso.inv_hom_id_app_assoc] using h'.symm
  change DerivedCategory.Q.{w}.map (roosι M) ≫ DerivedCategory.Q.{w}.map (σ.inv.app M) ≫
    β.hom.app M = _
  rw [← DerivedCategory.Q.{w}.map_comp_assoc, hs, DerivedCategory.Q.{w}.map_comp,
    Category.assoc]
  exact congrArg (fun z ↦ DerivedCategory.Q.{w}.map (o.inv.app M) ≫ z) (congr_app hβ M)

private theorem normalized_roos_iso_unique
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    [HasExactLimitsOfShape (Discrete ℕ) A] :
    ∃! e : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        DerivedCategory.Q.{w}.obj (strictRoosComplex M) ≅
          (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.obj (DerivedCategory.Q.{w}.obj M),
      (∀ (M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a : M ⟶ N),
        DerivedCategory.Q.{w}.map (roosF.map a) ≫ (e N).hom =
          (e M).hom ≫ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.map
            (DerivedCategory.Q.{w}.map a)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
        DerivedCategory.Q.{w}.map (roosι I) ≫ (e I).hom =
          DerivedCategory.Q.{w}.map (ExactAdjointTowerModels.ordinaryIso.inv.app I) ≫
            ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).inv) := by
  classical
  let F : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  obtain ⟨e, he⟩ := normalized_roos_iso (A := A)
  have hn (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
      DerivedCategory.Q.{w}.map (roosι I) ≫ e.hom.app I =
        DerivedCategory.Q.{w}.map (ExactAdjointTowerModels.ordinaryIso.inv.app I) ≫
          (F.rightDerivedFunctorObjQIso I).inv := by
    exact (he I).trans (congrArg
      (fun z ↦ DerivedCategory.Q.{w}.map (ExactAdjointTowerModels.ordinaryIso.inv.app I) ≫ z)
      (F.rightDerivedFunctorUnitQ_eq I))
  refine ⟨fun M ↦ e.app M, ⟨?_, ?_⟩, ?_⟩
  · intro M N a
    exact e.hom.naturality a
  · intro I hI
    exact hn I
  · intro e' he'
    apply sfRoosComparison_ext e' (fun M ↦ e.app M) he'.1
      (fun _ _ a ↦ e.hom.naturality a)
    intro I hI
    apply Iso.ext
    have : IsIso (DerivedCategory.Q.{w}.map (roosι I) ≫ e.hom.app I) := by
      rw [hn I]
      infer_instance
    have : IsIso (DerivedCategory.Q.{w}.map (roosι I)) :=
      IsIso.of_isIso_comp_right _ (e.hom.app I)
    apply (cancel_epi (DerivedCategory.Q.{w}.map (roosι I))).mp
    exact (he'.2 I).trans (hn I).symm


private theorem component_iso_eqToIso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (h : F = G) (hobj : ∀ X, F.obj X = G.obj X)
    (hn : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (eqToIso (hobj Y)).hom = (eqToIso (hobj X)).hom ≫ G.map f) :
    NatIso.ofComponents (fun X ↦ eqToIso (hobj X)) hn = eqToIso h := by
  cases h
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rfl

private theorem exact_left_derived_iso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G F : A ⥤ B) [G.Additive] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))]
    (μ : G ≅ F) :
    ∃! e : L ≅ F.mapDerivedCategory,
      whiskerLeft DerivedCategory.Qh e.hom ≫ F.mapDerivedCategoryFactorsh.hom =
        ε ≫ whiskerRight (NatTrans.mapHomotopyCategory μ.hom (.up ℤ))
          DerivedCategory.Qh := by
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let m : G.mapHomotopyCategory (.up ℤ) ≅ F.mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory μ.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory μ.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  let τ := isoWhiskerRight m DerivedCategory.Qh
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactorsh
  let e : L ≅ F.mapDerivedCategory := Functor.leftDerivedNatIso L F.mapDerivedCategory ε
    F.mapDerivedCategoryFactorsh.hom W τ
  have he : whiskerLeft DerivedCategory.Qh e.hom ≫ F.mapDerivedCategoryFactorsh.hom =
      ε ≫ τ.hom := Functor.leftDerivedNatTrans_fac L F.mapDerivedCategory ε
        F.mapDerivedCategoryFactorsh.hom W τ.hom
  exact ⟨e, he, fun e' he' ↦ Iso.ext
    (Functor.leftDerived_ext F.mapDerivedCategory F.mapDerivedCategoryFactorsh.hom W L
      e'.hom e.hom (he'.trans he.symm))⟩

-- This generic certificate identifies the canonical product comparison with the
-- original projection formula, for any proof of evaluation compatibility.
private theorem roos_product_comparison_formula
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (h : ∀ n : ℕ, (F.mapHomologicalComplex (.up ℤ)).obj (M.asFunctor.obj (op n)) =
      ((roosTowerAction F).obj M).asFunctor.obj (op n)) :
    Pi.lift (f := fun n : ℕ ↦ ((roosTowerAction F).obj M).asFunctor.obj (op n))
      (fun n : ℕ ↦ (F.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n) ≫ eqToHom (h n)) =
      roosProductComparison F M := by
  apply Pi.hom_ext
  intro n
  simp only [roosProductComparison, piComparison, Pi.lift_π,
    eqToHom_refl, Category.comp_id]
  change (F.mapHomologicalComplex (.up ℤ)).map
      (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n) =
    (Pi.lift (fun k : ℕ ↦ (F.mapHomologicalComplex (.up ℤ)).map
      (Pi.π (fun j : ℕ ↦ M.asFunctor.obj (op j)) k))) ≫
        Pi.π (fun k : ℕ ↦ (F.mapHomologicalComplex (.up ℤ)).obj
          (M.asFunctor.obj (op k))) n
  rw [Pi.lift_π]

private theorem roos_iso_unique
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃! e : (F.mapHomologicalComplex (.up ℤ)).obj (strictRoosComplex M) ≅
        strictRoosComplex
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj M),
      ∀ p : ℤ, e.hom.f (p + 1) ≫
          (strictRoosCoordinates
            ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj M)
            p).hom =
        F.map (strictRoosCoordinates M p).hom ≫ biprodComparison F _ _ ≫
          biprod.map ((roosProductComparison F M).f p)
            ((roosProductComparison F M).f (p + 1)) := by
  have := roosAdditiveComparison_isIso F M
  refine ⟨asIso (roosAdditiveComparison F M), ?_, ?_⟩
  · exact fun p ↦ roosAdditiveComparison_coordinates F M p
  · intro e he
    apply Iso.ext
    ext k : 1
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    apply (cancel_mono (strictRoosCoordinates
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj M)
      p).hom).1
    exact (he p).trans (roosAdditiveComparison_coordinates F M p).symm

namespace AlgebraicGeometry.Scheme.ImmersionCompletedPullback

private theorem normalized_exact_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (he : F = G) (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : L ≅ G.mapDerivedCategory)
    (hnorm : whiskerLeft DerivedCategory.Qh e.hom ≫ G.mapDerivedCategoryFactorsh.hom =
      ε ≫ whiskerRight (NatTrans.mapHomotopyCategory (eqToIso he).hom (.up ℤ))
        DerivedCategory.Qh)
    (hp : ∀ P : CochainComplex C ℤ, (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P) :
    ExactDerivedCounitNormalization F G L
      (Functor.leftDerivedCounitOnComplex F L ε) hp e := by
  cases he
  intro P
  have h := congr_app hnorm ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.mapHomotopyCategory_id,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, NatTrans.id_app,
    DerivedCategory.Qh.map_id] at h
  erw [Category.comp_id] at h
  have hn := e.hom.naturality ((DerivedCategory.quotientCompQhIso C).inv.app P)
  try dsimp only [Functor.comp_map] at hn
  simp only [eqToIso_refl, Iso.refl_hom, DerivedCategory.Q.map_id, Category.comp_id]
  dsimp only [Functor.leftDerivedCounitOnComplex]
  rw [← h, F.mapDerivedCategoryFactorsh_hom_app]
  simp only [← Category.assoc]
  erw [hn]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  simp

end AlgebraicGeometry.Scheme.ImmersionCompletedPullback
