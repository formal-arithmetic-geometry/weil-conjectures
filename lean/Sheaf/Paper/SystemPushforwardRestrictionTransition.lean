/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.CategoryTheory.DerivedExactSquareComposition

/-! # Restriction transitions of simultaneous derived direct image

Source: Stacks Project, Tag 0D6E, lemma-derived-pushforward-composition, and the
coefficient-square calculation using Tags 07A6 and 0D6D
(blueprint: lem-pur-system-pushforward-restriction-transition).

The site has object universe u+1 and morphism universe u. The supplied Geometry
is the normalized geometric calculus of the semilinear-derived-sections theorem.
The restriction comparison is constructed by conjugating its coefficient pullback;
the theorem identifies its inverse with the ring-change mate and fixes its
K-injective normalization independently of the system transition formula.

## Main definitions and statements

- `systemRestrictionPullback`: exact localized inverse-image comparison.
- `systemOrdinaryRestrictionPushforward`: its ordinary direct-image mate.
- `systemRestrictionComparison`: the comparison delta in system coordinates.
- `systemPushforwardRestrictionTransition`: transition, resolution and scalar formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u c v r

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

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

section ResolutionCalculation

variable {X₀ X₁ Y₀ Y₁ : Type*}
  [Category X₀] [Category X₁] [Category Y₀] [Category Y₁]
  [Abelian X₀] [Abelian X₁] [Abelian Y₀] [Abelian Y₁]
  [HasDerivedCategory X₀] [HasDerivedCategory X₁]
  [HasDerivedCategory Y₀] [HasDerivedCategory Y₁]
  [Abelian.HasKInjectiveResolutions Y₀] [Abelian.HasKInjectiveResolutions Y₁]
  {F₀ : X₀ ⥤ Y₀} {R₀ : Y₀ ⥤ X₀} {F₁ : X₁ ⥤ Y₁} {R₁ : Y₁ ⥤ X₁}
  {p : X₀ ⥤ X₁} {q : Y₀ ⥤ Y₁}
  [F₀.Additive] [R₀.Additive] [F₁.Additive] [R₁.Additive] [p.Additive] [q.Additive]
  [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits q] [PreservesFiniteColimits q]

private theorem derived_unit_inv (R : Y₀ ⥤ X₀) [R.Additive]
    (I : CochainComplex Y₀ ℤ) [I.IsKInjective] :
    chainDerivedUnit R I = (R.rightDerivedFunctorObjQIso I).inv := by
  simp only [chainDerivedUnit, Functor.rightDerivedFunctorObjQIso,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, asIso_hom, Iso.app_hom,
    quotient_inv_id, quotient_hom_id, Category.id_comp]

private theorem mate_resolution (a₀ : F₀ ⊣ R₀) (a₁ : F₁ ⊣ R₁)
    (β : p ⋙ F₁ ≅ F₀ ⋙ q)
    (I : CochainComplex Y₀ ℤ) [I.IsKInjective]
    (H : CochainComplex Y₁ ℤ) [H.IsKInjective]
    (j : (q.mapHomologicalComplex (.up ℤ)).obj I ⟶ H) :
    (mateEquiv a₀.mapDerivedCategoryRightDerivedAdjunction
      a₁.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        ((Functor.mapDerivedCategoryCompIso p F₁).symm ≪≫
          Functor.mapDerivedCategoryNatIso β ≪≫
          Functor.mapDerivedCategoryCompIso F₀ q).hom)).natTrans.app (DerivedCategory.Q.obj I) ≫
      R₁.rightDerivedFunctor.map
        (q.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map j) =
    p.mapDerivedCategory.map (R₀.rightDerivedFunctorObjQIso I).hom ≫
      p.mapDerivedCategoryFactors.hom.app ((R₀.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans (.up ℤ)).app I) ≫
      DerivedCategory.Q.map ((R₁.mapHomologicalComplex (.up ℤ)).map j) ≫
      (R₁.rightDerivedFunctorObjQIso H).inv := by
  have hf := derived_mate_factors a₀ a₁ β I
  have hn := R₁.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ _).map j)
  dsimp only [Functor.comp_map] at hn
  have he (K : CochainComplex Y₁ ℤ) : chainDerivedUnit R₁ K =
      R₁.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) := by
    dsimp only [chainDerivedUnit]
    rw [quotient_inv_id, quotient_hom_id]
    erw [R₁.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  rw [← he H, ← he ((q.mapHomologicalComplex (.up ℤ)).obj I)] at hn
  change DerivedCategory.Q.map ((R₁.mapHomologicalComplex (.up ℤ)).map j) ≫
      chainDerivedUnit R₁ H =
    chainDerivedUnit R₁ ((q.mapHomologicalComplex (.up ℤ)).obj I) ≫
      R₁.rightDerivedFunctor.map (DerivedCategory.Q.map j) at hn
  apply (cancel_epi (p.mapDerivedCategory.map (R₀.rightDerivedFunctorObjQIso I).inv)).1
  simp only [← p.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id,
    p.mapDerivedCategory.map_id, Category.id_comp]
  rw [← derived_unit_inv R₀ I, Functor.map_comp]
  erw [reassoc_of% hf]
  have hn' := congrArg (fun f ↦
    p.mapDerivedCategoryFactors.hom.app ((R₀.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans (.up ℤ)).app I) ≫ f)
      hn.symm
  simpa only [Category.assoc, derived_unit_inv R₁ H] using hn'

private theorem mate_resolution_quasiIso (a₀ : F₀ ⊣ R₀) (a₁ : F₁ ⊣ R₁)
    (β : p ⋙ F₁ ≅ F₀ ⋙ q)
    [IsIso (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans]
    (I : CochainComplex Y₀ ℤ) [I.IsKInjective]
    (H : CochainComplex Y₁ ℤ) [H.IsKInjective]
    (j : (q.mapHomologicalComplex (.up ℤ)).obj I ⟶ H) [QuasiIso j]
    (hd : IsIso ((mateEquiv a₀.mapDerivedCategoryRightDerivedAdjunction
      a₁.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        ((Functor.mapDerivedCategoryCompIso p F₁).symm ≪≫
          Functor.mapDerivedCategoryNatIso β ≪≫
          Functor.mapDerivedCategoryCompIso F₀ q).hom)).natTrans.app (DerivedCategory.Q.obj I))) :
    QuasiIso ((R₁.mapHomologicalComplex (.up ℤ)).map j) := by
  have := hd
  have h := mate_resolution a₀ a₁ β I H j
  have : IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans (.up ℤ)).app I)) := by
    change IsIso (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex
        (asIso (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans) (.up ℤ)).hom.app I))
    infer_instance
  have hi : IsIso (
      p.mapDerivedCategory.map (R₀.rightDerivedFunctorObjQIso I).hom ≫
      p.mapDerivedCategoryFactors.hom.app ((R₀.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans (.up ℤ)).app I) ≫
      DerivedCategory.Q.map ((R₁.mapHomologicalComplex (.up ℤ)).map j) ≫
      (R₁.rightDerivedFunctorObjQIso H).inv) := by
    rw [← h]
    infer_instance
  have : IsIso
      (DerivedCategory.Q.map ((R₁.mapHomologicalComplex (.up ℤ)).map j) ≫
        (R₁.rightDerivedFunctorObjQIso H).inv) := by
    let f := p.mapDerivedCategory.map (R₀.rightDerivedFunctorObjQIso I).hom ≫
      p.mapDerivedCategoryFactors.hom.app ((R₀.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans (.up ℤ)).app I)
    have : IsIso f := by dsimp only [f]; infer_instance
    have : IsIso (f ≫ DerivedCategory.Q.map
        ((R₁.mapHomologicalComplex (.up ℤ)).map j) ≫
        (R₁.rightDerivedFunctorObjQIso H).inv) := by
      simpa only [f, Category.assoc] using hi
    exact IsIso.of_isIso_comp_left f _
  have hi₄ := IsIso.of_isIso_comp_right
    (DerivedCategory.Q.map ((R₁.mapHomologicalComplex (.up ℤ)).map j))
    (R₁.rightDerivedFunctorObjQIso H).inv
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hi₄

end ResolutionCalculation

section MateCalculation

variable {X₀ X₁ Y₀ Y₁ : Type*}
  [Category X₀] [Category X₁] [Category Y₀] [Category Y₁]
  {F₀ : X₀ ⥤ Y₀} {R₀ : Y₀ ⥤ X₀} {F₁ : X₁ ⥤ Y₁} {R₁ : Y₁ ⥤ X₁}
  {T : X₀ ⥤ X₁} {p : X₁ ⥤ X₀} {S : Y₀ ⥤ Y₁} {q : Y₁ ⥤ Y₀}
  (a₀ : F₀ ⊣ R₀) (a₁ : F₁ ⊣ R₁) (t : T ⊣ p) (s : S ⊣ q)

private theorem scalar_mate_transpose (χ : T ⋙ F₁ ≅ F₀ ⋙ S)
    (M : Y₀) (L : Y₁) (a : M ⟶ q.obj L) :
    (t.homEquiv _ _).symm
        (R₀.map a ≫ (conjugateIsoEquiv (a₀.comp s) (t.comp a₁) χ).hom.app L) =
      (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ χ.hom)).app M ≫
        R₁.map ((s.homEquiv _ _).symm a) := by
  change (t.homEquiv _ _).symm
    (R₀.map a ≫ (conjugateEquiv (a₀.comp s) (t.comp a₁) χ.hom).app L) = _
  rw [← iterated_mateEquiv_conjugateEquiv a₀ a₁ t s]
  rw [t.homEquiv_counit, Functor.map_comp, Category.assoc,
    mateEquiv_counit s t]
  have hn := (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ χ.hom)).naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [s.homEquiv_counit, Functor.map_comp, Category.assoc]

private theorem restriction_mate (χ : T ⋙ F₁ ≅ F₀ ⋙ S)
    (β : p ⋙ F₀ ≅ F₁ ⋙ q)
    (hχ : ∀ P, (s.homEquiv _ _) (χ.inv.app P) =
      F₀.map (t.unit.app P) ≫ β.hom.app (T.obj P)) :
    (conjugateIsoEquiv (a₀.comp s) (t.comp a₁) χ).inv =
      (mateEquiv a₁ a₀ (TwoSquare.mk _ _ _ _ β.hom)).natTrans := by
  have hb : mateEquiv t s (TwoSquare.mk _ _ _ _ χ.inv) =
      TwoSquare.mk _ _ _ _ β.hom := by
    apply (mateEquiv t s).symm.injective
    simp only [Equiv.symm_apply_apply]
    ext P
    apply (s.homEquiv _ _).injective
    rw [hχ]
    simpa only [s.homEquiv_unit, TwoSquare.mk, TwoSquare.natTrans,
      Functor.id_obj, Functor.comp_obj] using
      (unit_mateEquiv_symm t s (TwoSquare.mk _ _ _ _ β.hom) P)
  change conjugateEquiv (t.comp a₁) (a₀.comp s) χ.inv = _
  rw [← iterated_mateEquiv_conjugateEquiv t s a₀ a₁, hb]

end MateCalculation

section TransitionCalculation

variable {C D X₀ X₁ Y₀ Y₁ : Type*}
  [Category C] [Category D] [Category X₀] [Category X₁] [Category Y₀] [Category Y₁]
  {U : C ⥤ D} {H : D ⥤ C}
  {A₀ : C ⥤ X₀} {A₁ : C ⥤ X₁} {B₀ : D ⥤ Y₀} {B₁ : D ⥤ Y₁}
  {F₀ : X₀ ⥤ Y₀} {R₀ : Y₀ ⥤ X₀} {F₁ : X₁ ⥤ Y₁} {R₁ : Y₁ ⥤ X₁}
  {p : X₁ ⥤ X₀} {q : Y₁ ⥤ Y₀}

private theorem transition_mate (adj : U ⊣ H) (adj₀ : F₀ ⊣ R₀) (adj₁ : F₁ ⊣ R₁)
    (a₀ : U ⋙ B₀ ≅ A₀ ⋙ F₀) (a₁ : U ⋙ B₁ ≅ A₁ ⋙ F₁)
    (b₀ : H ⋙ A₀ ≅ B₀ ⋙ R₀) (b₁ : H ⋙ A₁ ≅ B₁ ⋙ R₁)
    (c₀ : ∀ N, F₀.map (b₀.hom.app N) ≫ adj₀.counit.app (B₀.obj N) =
      a₀.inv.app (H.obj N) ≫ B₀.map (adj.counit.app N))
    (c₁ : ∀ N, F₁.map (b₁.hom.app N) ≫ adj₁.counit.app (B₁.obj N) =
      a₁.inv.app (H.obj N) ≫ B₁.map (adj.counit.app N))
    (τ : A₀ ⟶ A₁ ⋙ p) (σ : B₀ ⟶ B₁ ⋙ q) (β : p ⋙ F₀ ≅ F₁ ⋙ q)
    (ht : ∀ M, σ.app (U.obj M) ≫ q.map (a₁.hom.app M) =
      a₀.hom.app M ≫ F₀.map (τ.app M) ≫ β.hom.app (A₁.obj M))
    (N : D) :
    τ.app (H.obj N) ≫ p.map (b₁.hom.app N) ≫
        (mateEquiv adj₁ adj₀ (TwoSquare.mk _ _ _ _ β.hom)).app (B₁.obj N) =
      b₀.hom.app N ≫ R₀.map (σ.app N) := by
  apply (adj₀.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit adj₁ adj₀]
  have hn := β.hom.naturality (b₁.hom.app N)
  dsimp only [Functor.comp_map] at hn
  simp only [TwoSquare.mk]
  rw [reassoc_of% hn]
  simp only [← q.map_comp]
  rw [c₁]
  have ht' := congrArg (fun f ↦ a₀.inv.app (H.obj N) ≫ f) (ht (H.obj N))
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at ht'
  rw [← reassoc_of% ht']
  simp only [q.map_comp, ← q.map_comp_assoc, Iso.hom_inv_id_app]
  erw [q.map_id, Category.id_comp]
  have hσ := σ.naturality (adj.counit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hσ
  rw [← hσ]
  have hc := adj₀.counit.naturality (σ.app N)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hc
  rw [hc]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ σ.app N) (c₀ N).symm

end TransitionCalculation

namespace WeilConjectures.SemilinearSections

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

end WeilConjectures.SemilinearSections

namespace WeilConjectures.SemilinearSections.Geometry

variable {V W : Scheme.{u}}
  [EssentiallySmall.{u + 1} V.ProEt] [EssentiallySmall.{u + 1} W.ProEt]
  [EssentiallySmall.{u + 1} (ℕ × V.ProEt)] [EssentiallySmall.{u + 1} (ℕ × W.ProEt)]
  (u : V ⟶ W)
  (B : ℕ → Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  (A : Data.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ)
  (G : Geometry.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ A
    (Scheme.ProEt.topology V) (Scheme.proEtaleSheafInverseImage u (Type (u + 1)))
    (Scheme.proEtaleSheafDirectImage u (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction u (Type (u + 1))))

/-- The localized identity-on-underlying-sheaves coefficient restriction comparison.
Source: Stacks 0D6D; normalized geometric calculus
(blueprint: lem-pur-system-pushforward-restriction-transition). -/
def systemRestrictionPullback {m n : ℕ} (h : n ≤ m) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (G.restrictionPullback h) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The ordinary direct-image comparison for the two coefficient factorizations.
It is the mate of the actual identity-on-underlying-sheaves inverse-image comparison.
Source: Stacks 07A6 and 0D6E
(blueprint: lem-pur-system-pushforward-restriction-transition). -/
def systemOrdinaryRestrictionPushforward {m n : ℕ} (h : n ≤ m) :=
  (mateEquiv (G.levelAdjunction n) (G.levelAdjunction m)
    (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom)).natTrans

/-- The restriction-form comparison delta, constructed from normalized adjunctions.
The theorem below identifies its inverse with the canonical ring-change comparison
and characterizes it on every K-injective replacement, without preservation of
K-injectives by scalar restriction.
Source: Stacks 07A6, 0D6D and 0D6E
(blueprint: lem-pur-system-pushforward-restriction-transition). -/
def systemRestrictionComparison {m n : ℕ} (h : n ≤ m) :=
  conjugateIsoEquiv ((G.derivedLevelAdjunction m).comp (G.target.scalar h).adjunction)
    ((A.scalar h).adjunction.comp (G.derivedLevelAdjunction n))
    (G.coefficientPullback h)

private theorem pull_transition {m n : ℕ} (h : n ≤ m)
    (M : DS.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ) :
    (derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
      G.coefficients G.coefficientTransition h).app
        (G.pull.mapDerivedCategory.obj M) ≫
      (resD.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
        G.coefficients G.coefficientTransition h)).map ((G.pullEvaluation n).hom.app M) =
    (G.pullEvaluation m).hom.app M ≫
      (G.inverseImage m).modules.mapDerivedCategory.map
        ((derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h).app M) ≫
      (systemRestrictionPullback u B τ A G h).hom.app
        ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ n).obj M) := by
  rw [G.pullEvaluation_model n, G.pullEvaluation_model m]
  exact localize_transition G.pull
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ m)
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ n)
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
      G.coefficients G.coefficientTransition m)
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
      G.coefficients G.coefficientTransition n)
    (G.inverseImage m).modules (G.inverseImage n).modules
    (res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1}
      (Scheme.ProEt.topology W) B τ h))
    (res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1}
      (Scheme.ProEt.topology V) G.coefficients G.coefficientTransition h))
    (G.ordinaryPullEvaluation m) (G.ordinaryPullEvaluation n) (G.restrictionPullback h)
    (transition.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)
    (transition.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
      G.coefficients G.coefficientTransition h)
    (derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)
    (derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
      G.coefficients G.coefficientTransition h)
    (derived_transition_fac.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)
    (derived_transition_fac.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
      G.coefficients G.coefficientTransition h)
    (G.ordinaryPullTransition h) M

omit [EssentiallySmall.{u + 1} (ℕ × V.ProEt)]
  [EssentiallySmall.{u + 1} (ℕ × W.ProEt)] in
private theorem level_adjunction_underlying (n : ℕ)
    (M : Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W) (B n))
    (N : Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n))
    (f : (G.inverseImage n).modules.obj M ⟶ N) :
    (underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology W) (B n)).map
        ((G.levelAdjunction n).homEquiv M N f) ≫
      (G.levelPushUnderlying n).hom.app N =
    (Scheme.proEtaleSheafAdjunction u (Type (u + 1))).homEquiv _ _
      ((G.inverseImage n).moduleUnderlying.inv.app M ≫
        (underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n)).map f) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := (G.levelPushUnderlying n).hom.naturality f
  change (underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology W) (B n)).map
      ((G.levelPush n).map f) ≫ (G.levelPushUnderlying n).hom.app N =
    (G.levelPushUnderlying n).hom.app ((G.inverseImage n).modules.obj M) ≫
      (Scheme.proEtaleSheafDirectImage u (Type (u + 1))).map
        ((underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
          (G.coefficients n)).map f) at hn
  rw [Category.assoc, hn]
  change _ = _ ≫ (Scheme.proEtaleSheafDirectImage u (Type (u + 1))).map _
  rw [← G.level_unit_underlying n M, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]

omit [EssentiallySmall.{u + 1} (ℕ × V.ProEt)]
  [EssentiallySmall.{u + 1} (ℕ × W.ProEt)] in
private theorem ordinary_mate_underlying {m n : ℕ} (h : n ≤ m)
    (N : Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n)) :
    (underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology W) (B m)).map
        ((systemOrdinaryRestrictionPushforward u B τ A G h).app N) ≫
      (G.levelPushUnderlying m).hom.app
        ((res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
          G.coefficients G.coefficientTransition h)).obj N) =
      (G.levelPushUnderlying n).hom.app N := by
  let q := res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
    G.coefficients G.coefficientTransition h)
  let p := res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)
  let f := (G.restrictionPullback h).hom.app ((G.levelPush n).obj N) ≫
    q.map ((G.levelAdjunction n).counit.app N)
  have hm : (G.levelAdjunction m).homEquiv _ _ f =
      (systemOrdinaryRestrictionPushforward u B τ A G h).app N := by
    apply ((G.levelAdjunction m).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit (G.levelAdjunction n) (G.levelAdjunction m)
      (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom) N).symm
  rw [← hm]
  erw [level_adjunction_underlying u B τ A G m _ _ f]
  have hf : (G.inverseImage m).moduleUnderlying.inv.app
      (p.obj ((G.levelPush n).obj N)) ≫
      (underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients m)).map f =
    (G.inverseImage n).moduleUnderlying.inv.app ((G.levelPush n).obj N) ≫
      (underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n)).map
        ((G.levelAdjunction n).counit.app N) := by
    have hr := G.restrictionPullback_underlying h ((G.levelPush n).obj N)
    have hr' : (underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients m)).map
        ((G.restrictionPullback h).hom.app ((G.levelPush n).obj N)) =
      (G.inverseImage m).moduleUnderlying.hom.app (p.obj ((G.levelPush n).obj N)) ≫
        (G.inverseImage n).moduleUnderlying.inv.app ((G.levelPush n).obj N) := by
      apply (cancel_mono ((G.inverseImage n).moduleUnderlying.hom.app _)).1
      rw [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      exact hr
    dsimp only [f]
    rw [Functor.map_comp, hr']
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rfl
  refine (congrArg ((Scheme.proEtaleSheafAdjunction u (Type (u + 1))).homEquiv _ _)
    hf).trans ?_
  refine (level_adjunction_underlying u B τ A G n ((G.levelPush n).obj N) N
    ((G.levelAdjunction n).counit.app N)).symm.trans ?_
  have hc : (G.levelAdjunction n).homEquiv ((G.levelPush n).obj N) N
      ((G.levelAdjunction n).counit.app N) = 𝟙 _ := by
    apply ((G.levelAdjunction n).homEquiv _ N).symm.injective
    rw [Equiv.symm_apply_apply]
    exact (Adjunction.homEquiv_symm_id (G.levelAdjunction n) N).symm
  rw [hc, CategoryTheory.Functor.map_id, Category.id_comp]

omit [EssentiallySmall.{u + 1} (ℕ × V.ProEt)]
  [EssentiallySmall.{u + 1} (ℕ × W.ProEt)] in
private theorem ordinary_mate_isIso {m n : ℕ} (h : n ≤ m) :
    IsIso (systemOrdinaryRestrictionPushforward u B τ A G h) := by
  have hi (N : Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n)) :
      IsIso ((systemOrdinaryRestrictionPushforward u B τ A G h).app N) := by
    have he := ordinary_mate_underlying u B τ A G h N
    have : IsIso ((underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology W) (B m)).map
        ((systemOrdinaryRestrictionPushforward u B τ A G h).app N) ≫
        (G.levelPushUnderlying m).hom.app
          ((res.{u + 1, u, u + 1} (coefficientMap.{u + 1, u, u + 1}
            (Scheme.ProEt.topology V) G.coefficients G.coefficientTransition h)).obj N)) := by
      rw [he]
      infer_instance
    have : IsIso ((underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology W) (B m)).map
        ((systemOrdinaryRestrictionPushforward u B τ A G h).app N)) :=
      IsIso.of_isIso_comp_right _ ((G.levelPushUnderlying m).hom.app _)
    exact isIso_of_reflects_iso _
      (underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology W) (B m))
  have := hi
  exact NatIso.isIso_of_isIso_app _

set_option maxHeartbeats 1000000 in
-- Rewriting the two normalized derived adjunctions traverses large module-category instances.
/-- The actual restriction transition of simultaneous direct image is the canonical
resolution-normalized comparison followed by direct image of the original transition.
The last clause states its scalar transpose using exactly the two coefficient
adjunctions; the first clause identifies its inverse with ring-sheaf change.
Source: Stacks 0D6E (lemma-derived-pushforward-composition), 0D6D and 07A6
(blueprint: lem-pur-system-pushforward-restriction-transition).
Proof: (1) Apply ring-sheaf-change adjunction to the coefficient square B_m to B_n
and its inverse image C_m to C_n; exact scalar restrictions are its vertical sides
(lem-weil-pbc-ring-sheaf-change-adjunction).
(2) Compare the two ringed-topos factorizations. Adjunction-compatible pullback
composition identifies their right comparison with the conjugate of the normalized
coefficient pullback. On a flat-term K-flat representative both pullback comparisons
send x tensor lambda to lambda times inverse-image(x tensor 1), by the normalized
scalar unit and transpose formulas. This identifies the comparison with the one
whose mate is coefficientMate (lem-sfb-ringed-derived-monoidal-comparisons,
def-coef-semilinear-geometry-derived,
lem-pur-sheaf-ring-derived-coefficient-adjunction).
(3) Expand the composite adjunction unit and counit: delta_L is eta^T followed by
restriction of b at qL and then restriction of G_n applied to the scalar counit
(def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting).
(4) Naturality of the scalar unit and b gives the asserted transpose identity for
arbitrary M, L and a. The two scalar Hom equivalences are bijective.
(5) Apply the coherent-section extension-form transition theorem. Both its reductions
are scalar transposes of derivedTransition. Step (4) and injectivity of that Hom
bijection give the displayed restriction transition, including its evaluation maps
(lem-coef-semilinear-derived-sections).
(6) Apply the K-injective direct-image composition normalization to I and j:qI to H.
The lemma lem-weil-pbc-ringed-topoi-derived-pushforward-composition says that
direct image of j is a quasi-isomorphism, and that the comparison is
its class after the ordinary identity-on-sheaves comparison. The displayed square
writes all localization and K-injective identifications explicitly. Every map used
is natural. Equal levels give identity coefficient maps and identity comparisons;
zero systems and non-flat tower maps require no additional argument or assumptions.
No faithfulness of derived evaluation or preservation of K-injectives by evaluation
or scalar restriction is used. -/
theorem systemPushforwardRestrictionTransition {m n : ℕ} (h : n ≤ m) :
    (systemRestrictionComparison u B τ A G h).inv =
      (mateEquiv (G.derivedLevelAdjunction n) (G.derivedLevelAdjunction m)
        (TwoSquare.mk _ _ _ _ (systemRestrictionPullback u B τ A G h).hom)).natTrans ∧
    (∀ N : DS.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
        G.coefficients G.coefficientTransition,
      (derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h).app
          (G.push.rightDerivedFunctor.obj N) ≫
        (resD.{u + 1, u, u + 1}
          (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)).map
            ((G.pushEvaluation n).hom.app N) =
      (G.pushEvaluation m).hom.app N ≫
        (G.levelPush m).rightDerivedFunctor.map
          ((derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
            G.coefficients G.coefficientTransition h).app N) ≫
        (systemRestrictionComparison u B τ A G h).hom.app
          ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
            G.coefficients G.coefficientTransition n).obj N)) ∧
    (∀ (I : CochainComplex
        (Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n)) ℤ)
        [I.IsKInjective]
        (H : CochainComplex
          (Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients m)) ℤ)
        [H.IsKInjective]
        (j : ((res.{u + 1, u, u + 1}
          (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
            G.coefficients G.coefficientTransition h)).mapHomologicalComplex (.up ℤ)).obj I ⟶ H)
        [QuasiIso j],
      QuasiIso (((G.levelPush m).mapHomologicalComplex (.up ℤ)).map j) ∧
      (systemRestrictionComparison u B τ A G h).inv.app (DerivedCategory.Q.{u + 2}.obj I) ≫
        (G.levelPush m).rightDerivedFunctor.map
          ((res.{u + 1, u, u + 1}
              (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
                G.coefficients G.coefficientTransition h)).mapDerivedCategoryFactors.hom.app I ≫
            DerivedCategory.Q.{u + 2}.map j) =
      (resD.{u + 1, u, u + 1}
          (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)).map
            ((G.levelPush n).rightDerivedFunctorObjQIso I).hom ≫
        (Functor.mapDerivedCategoryFactors
          (res.{u + 1, u, u + 1}
            (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h))).hom.app
              (((G.levelPush n).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.{u + 2}.map
          ((NatTrans.mapHomologicalComplex
            (systemOrdinaryRestrictionPushforward u B τ A G h) (.up ℤ)).app I) ≫
        DerivedCategory.Q.{u + 2}.map (((G.levelPush m).mapHomologicalComplex (.up ℤ)).map j) ≫
        ((G.levelPush m).rightDerivedFunctorObjQIso H).inv) ∧
    (∀ (M : D.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients m))
        (L : D.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n))
        (a : M ⟶ (resD.{u + 1, u, u + 1}
          (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
            G.coefficients G.coefficientTransition h)).obj L),
      ((A.scalar h).adjunction.homEquiv _ _).symm
          ((G.levelPush m).rightDerivedFunctor.map a ≫
            (systemRestrictionComparison u B τ A G h).hom.app L) =
        (G.coefficientMate (Scheme.ProEt.topology W) B τ A (Scheme.ProEt.topology V)
          (Scheme.proEtaleSheafInverseImage u (Type (u + 1)))
          (Scheme.proEtaleSheafDirectImage u (Type (u + 1)))
          (Scheme.proEtaleSheafAdjunction u (Type (u + 1))) h).app M ≫
        (G.levelPush n).rightDerivedFunctor.map
          (((G.target.scalar h).adjunction.homEquiv _ _).symm a)) := by
  have hd := restriction_mate (G.derivedLevelAdjunction m) (G.derivedLevelAdjunction n)
    (A.scalar h).adjunction (G.target.scalar h).adjunction (G.coefficientPullback h)
    (systemRestrictionPullback u B τ A G h) (G.coefficientPullback_transpose h)
  change (systemRestrictionComparison u B τ A G h).inv = _ at hd
  refine ⟨hd, ?_, ?_, ?_⟩
  · intro N
    apply (cancel_mono ((systemRestrictionComparison u B τ A G h).inv.app
      ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology V) G.coefficients
        G.coefficientTransition n).obj N))).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    rw [hd]
    exact transition_mate G.adjunction (G.derivedLevelAdjunction m)
      (G.derivedLevelAdjunction n) (G.pullEvaluation m) (G.pullEvaluation n)
      (G.pushEvaluation m) (G.pushEvaluation n) (G.counit_evaluation m)
      (G.counit_evaluation n) (derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)
      (derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
      G.coefficients G.coefficientTransition h)
      (systemRestrictionPullback u B τ A G h) (pull_transition u B τ A G h) N
  · intro I _ H _ j _
    refine ⟨?_, ?_⟩
    · have : IsIso (mateEquiv (G.levelAdjunction n) (G.levelAdjunction m)
          (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom)).natTrans :=
        ordinary_mate_isIso u B τ A G h
      apply mate_resolution_quasiIso (G.levelAdjunction n) (G.levelAdjunction m)
        (G.restrictionPullback h) I H j
      rw [← G.derivedLevelAdjunction_canonical n, ← G.derivedLevelAdjunction_canonical m]
      change IsIso ((mateEquiv (G.derivedLevelAdjunction n) (G.derivedLevelAdjunction m)
        (TwoSquare.mk _ _ _ _ (systemRestrictionPullback u B τ A G h).hom)).natTrans.app
          (DerivedCategory.Q.obj I))
      have hi : IsIso ((systemRestrictionComparison u B τ A G h).inv.app
          (DerivedCategory.Q.obj I)) := inferInstance
      exact NatTrans.congr_app hd (DerivedCategory.Q.obj I) ▸ hi
    · have hr := mate_resolution (G.levelAdjunction n) (G.levelAdjunction m)
        (G.restrictionPullback h) I H j
      rw [← G.derivedLevelAdjunction_canonical n,
        ← G.derivedLevelAdjunction_canonical m] at hr
      erw [← NatTrans.congr_app hd (DerivedCategory.Q.obj I)] at hr
      exact hr
  · intro M L a
    exact scalar_mate_transpose (G.derivedLevelAdjunction m) (G.derivedLevelAdjunction n)
      (A.scalar h).adjunction (G.target.scalar h).adjunction
      (G.coefficientPullback h) M L a

end WeilConjectures.SemilinearSections.Geometry
