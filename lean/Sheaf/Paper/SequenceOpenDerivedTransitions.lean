/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SequenceSiteOpenData
import all Sheaf.CategoryTheory.DerivedExactSquareComposition

/-! # Derived transition compatibility for open extension

Source: Stacks Project, Tags 03DI, 03DJ and 05RU
(blueprint: lem-pur-sequence-open-derived-transitions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe c v r u s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
private theorem localize_transition
    {C D X₀ X₁ Y₀ Y₁ : Type*}
    [Category C] [Category D] [Category X₀] [Category X₁] [Category Y₀] [Category Y₁]
    [Abelian C] [Abelian D] [Abelian X₀] [Abelian X₁] [Abelian Y₀] [Abelian Y₁]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory X₀] [HasDerivedCategory X₁]
    [HasDerivedCategory Y₀] [HasDerivedCategory Y₁]
    (U : C ⥤ D) (E₀ : C ⥤ X₀) (E₁ : C ⥤ X₁)
    (B₀ : D ⥤ Y₀) (B₁ : D ⥤ Y₁) (F₀ : X₀ ⥤ Y₀) (F₁ : X₁ ⥤ Y₁)
    (p : X₁ ⥤ X₀) (q : Y₁ ⥤ Y₀)
    [U.Additive] [E₀.Additive] [E₁.Additive] [B₀.Additive] [B₁.Additive]
    [F₀.Additive] [F₁.Additive] [p.Additive] [q.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits B₀] [PreservesFiniteColimits B₀]
    [PreservesFiniteLimits B₁] [PreservesFiniteColimits B₁]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    (α₀ : U ⋙ B₀ ≅ E₀ ⋙ F₀) (α₁ : U ⋙ B₁ ≅ E₁ ⋙ F₁)
    (γ : p ⋙ F₀ ≅ F₁ ⋙ q) (τ : E₀ ⟶ E₁ ⋙ p) (σ : B₀ ⟶ B₁ ⋙ q)
    (t : E₀.mapDerivedCategory ⟶ E₁.mapDerivedCategory ⋙ p.mapDerivedCategory)
    (s : B₀.mapDerivedCategory ⟶ B₁.mapDerivedCategory ⋙ q.mapDerivedCategory)
    (tfac : ∀ K : CochainComplex C ℤ,
      t.app (DerivedCategory.Q.obj K) ≫
        p.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K) ≫
        p.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj K) =
      E₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))
    (sfac : ∀ K : CochainComplex D ℤ,
      s.app (DerivedCategory.Q.obj K) ≫
        q.mapDerivedCategory.map (B₁.mapDerivedCategoryFactors.hom.app K) ≫
        q.mapDerivedCategoryFactors.hom.app ((B₁.mapHomologicalComplex (.up ℤ)).obj K) =
      B₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app K))
    (htord : ∀ M, σ.app (U.obj M) ≫ q.map (α₁.hom.app M) =
      α₀.hom.app M ≫ F₀.map (τ.app M) ≫ γ.hom.app (E₁.obj M))
    (M : DerivedCategory C) :
    s.app (U.mapDerivedCategory.obj M) ≫
        q.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso α₁).hom.app M) =
      (Functor.mapDerivedCategorySquareIso α₀).hom.app M ≫
        F₀.mapDerivedCategory.map (t.app M) ≫
        (Functor.mapDerivedCategorySquareIso γ).hom.app (E₁.mapDerivedCategory.obj M) := by
  let a₀ := Functor.mapDerivedCategorySquareIso α₀
  let a₁ := Functor.mapDerivedCategorySquareIso α₁
  let β := Functor.mapDerivedCategorySquareIso γ
  let l : U.mapDerivedCategory ⋙ B₀.mapDerivedCategory ⟶
      (E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory) ⋙ q.mapDerivedCategory :=
    Functor.whiskerLeft U.mapDerivedCategory s ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight a₁.hom q.mapDerivedCategory
  let r : U.mapDerivedCategory ⋙ B₀.mapDerivedCategory ⟶
      (E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory) ⋙ q.mapDerivedCategory :=
    a₀.hom ≫ Functor.whiskerRight t F₀.mapDerivedCategory ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E₁.mapDerivedCategory β.hom ≫ (Functor.associator _ _ _).inv
  have hlr : l = r := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro K
    dsimp only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    let K₁ := (E₁.mapHomologicalComplex (.up ℤ)).obj K
    let UK := (U.mapHomologicalComplex (.up ℤ)).obj K
    have ha₀ := Functor.exactSquare_fac α₀ K
    have ha₁ := Functor.exactSquare_fac α₁ K
    have hβ := Functor.exactSquare_fac γ K₁
    have ht := tfac K
    have hs := sfac UK
    apply (cancel_mono
      (q.mapDerivedCategory.map
          (F₁.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K)) ≫
        q.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K₁) ≫
        q.mapDerivedCategoryFactors.hom.app
          ((F₁.mapHomologicalComplex (.up ℤ)).obj K₁))).1
    simp only [Category.assoc]
    have hnβ := β.hom.naturality (E₁.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hnβ
    erw [← reassoc_of% hnβ, hβ]
    rw [← F₀.mapDerivedCategory.map_comp_assoc,
      ← F₀.mapDerivedCategory.map_comp_assoc, Category.assoc]
    erw [ht]
    simp only [Functor.map_comp, Category.assoc]
    have hnF := F₀.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hnF
    erw [reassoc_of% hnF]
    erw [reassoc_of% ha₀]
    rw [← q.mapDerivedCategory.map_comp_assoc,
      ← q.mapDerivedCategory.map_comp_assoc, Category.assoc]
    erw [ha₁]
    simp only [Functor.map_comp, Category.assoc]
    have hnq := q.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex α₁.hom (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hnq
    erw [hnq]
    have hns := s.naturality (U.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hns
    erw [← reassoc_of% hns, reassoc_of% hs]
    have hord :
        (NatTrans.mapHomologicalComplex σ (.up ℤ)).app UK ≫
          (q.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex α₁.hom (.up ℤ)).app K) =
        (NatTrans.mapHomologicalComplex α₀.hom (.up ℤ)).app K ≫
          (F₀.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) ≫
          (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app K₁ := by
      ext i
      exact htord (K.X i)
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ B₀.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        B₀.mapDerivedCategoryFactors.hom.app UK ≫ DerivedCategory.Q.map f) hord
  simpa only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app hlr M

namespace WeilConjectures.SemilinearSections

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_transition_fac
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {m n : ℕ} (h : n ≤ m)
    (K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    (derivedTransition.{c, v, max c v r} J B τ h).app (DerivedCategory.Q.obj K) ≫
      (resD.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map
        ((Functor.mapDerivedCategoryFactors (evaluation.{c, v, max c v r} J B τ n)).hom.app K) ≫
      (Functor.mapDerivedCategoryFactors
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h))).hom.app
        (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj K) =
    (evaluation.{c, v, max c v r} J B τ m).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (transition.{c, v, max c v r} J B τ h) (.up ℤ)).app K) := by
  dsimp only [derivedTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Localization.liftNatTrans_app]
  simp only [Category.assoc]
  change _ ≫ _ ≫
    (Functor.mapDerivedCategoryFactors
      (evaluation.{c, v, max c v r} J B τ n ⋙
        res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h))).inv.app K ≫ _ = _
  simp only [Iso.inv_hom_id_app, Category.comp_id]
  rfl


private theorem replacement_fac
    {C A D : Type*} [Category C] [Category A] [Category D]
    [Abelian C] [Abelian A] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory D]
    (E₁ : C ⥤ A) (p q : A ⥤ D)
    [E₁.Additive] [p.Additive] [q.Additive]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    (T : C ⥤ D) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (τ : T ⟶ E₁ ⋙ p) (d : p ≅ q)
    (t : T.mapDerivedCategory ⟶ E₁.mapDerivedCategory ⋙ p.mapDerivedCategory)
    (ht : ∀ K : CochainComplex C ℤ,
      t.app (DerivedCategory.Q.obj K) ≫
        p.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K) ≫
        p.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj K) =
      T.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))
    (K : CochainComplex C ℤ) :
    (t ≫ Functor.whiskerLeft E₁.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso d).hom).app (DerivedCategory.Q.obj K) ≫
        q.mapDerivedCategory.map (E₁.mapDerivedCategoryFactors.hom.app K) ≫
        q.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj K) =
      T.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (τ ≫ Functor.whiskerLeft E₁ d.hom) (.up ℤ)).app K) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  have hn := (Functor.mapDerivedCategoryNatIso d).hom.naturality
    (E₁.mapDerivedCategoryFactors.hom.app K)
  rw [← reassoc_of% hn]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  erw [reassoc_of% (ht K)]
  rw [← Functor.map_comp]
  congr 1

set_option maxHeartbeats 800000 in
-- Exact-square specialization compares the independent site and coefficient universes.
/-- Ordinary level and coefficient transition equations descend to the specified
unbounded derived comparisons.
Source: Stacks 015F and 05RU (blueprint: lem-pur-sequence-open-derived-transitions).
Proof: apply each exact functor termwise and descend the ordinary transition identity
through the quasi-isomorphism localization. The evaluation and coefficient compositor
factors are retained throughout. Naturality moves the factors through each square;
after cancellation the assertion is Q applied to the ordinary identity in every degree.
Localization extensionality then gives equality on every derived object. -/
theorem SequenceOpenOrdinary.derivedTransitions {C : Type c} [Category.{v} C]
    [EssentiallySmall.{max c v r} C] (J : GrothendieckTopology C) (U : C)
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (O : SequenceOpenOrdinary.{c, v, r} J U B τ) (ht : O.Transitions) :
    O.DerivedTransitions := by
  let (n : ℕ) := SheafOfModules.localizedSystemExtensionAdditive.{c, v, r} (B n) U
  let (n : ℕ) := SheafOfModules.localizedSystemExtensionLimits.{c, v, r} (B n) U
  let (n : ℕ) := SheafOfModules.localizedSystemExtensionColimits.{c, v, r} (B n) U
  let (n : ℕ) := HasDerivedCategory.standard
    (SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J (B n)).over U))
  intro m n h M
  let E k := evaluation.{max c v, v, max c v r} (J.over U)
    (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) k
  let F k := evaluation.{c, v, max c v r} J B τ k
  let j k := SheafOfModules.localizedSystemExtension.{c, v, r} (B k) U
  let p := res (coefficientMap.{max c v, v, max c v r} (J.over U)
    (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) h)
  let p' := res ((J.overPullback CommRingCat.{max c v r} U).map
    (coefficientMap.{c, v, max c v r} J B τ h))
  let q := res (coefficientMap.{c, v, max c v r} J B τ h)
  let t := transition.{max c v, v, max c v r} (J.over U)
    (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) h
  let td := derivedTransition.{max c v, v, max c v r} (J.over U)
    (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) h
  have ht' := localize_transition O.Jfun (E m) (E n) (F m) (F n) (j m) (j n) p' q
    (O.level m) (O.level n)
    (O.coefficients.comparison (coefficientMap.{c, v, max c v r} J B τ h))
    (t ≫ Functor.whiskerLeft (E n) (O.coefficientRestriction h).hom)
    (transition.{c, v, max c v r} J B τ h)
    (td ≫ Functor.whiskerLeft (E n).mapDerivedCategory
      (Functor.mapDerivedCategoryNatIso (O.coefficientRestriction h)).hom)
    (derivedTransition.{c, v, max c v r} J B τ h)
    (by
      intro K
      -- Keep the localized restriction functors folded during this specialization.
      with_reducible exact (replacement_fac (E n) p p' (E m) t (O.coefficientRestriction h)
        td (derived_transition_fac.{max c v, v, max c v r} (J.over U)
          (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) h) K))
    (derived_transition_fac.{c, v, r} J B τ h)
    (by
      intro N
      simpa only [t, Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
        Category.assoc] using ht h N) M
  simpa only [SequenceOpenOrdinary.derivedLevel,
    SequenceOpenCoefficientData.derivedComparison, Functor.mapDerivedCategorySquareIso,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    using ht'

end WeilConjectures.SemilinearSections
