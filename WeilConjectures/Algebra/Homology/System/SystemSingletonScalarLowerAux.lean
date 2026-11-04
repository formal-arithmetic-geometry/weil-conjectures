/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarRepAux

/-! # Derived squares of exact functors and localized transitions

Abstract localization calculus for the singleton/scalar lower-map compatibility.
Source: functoriality of unbounded localization, Stacks 05S7
(blueprint: lem-pur-system-singleton-scalar-lower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Inverting a square of isomorphisms. -/
theorem iso_square_inv_inv {C' : Type*} [Category C'] {P P' R R' : C'} (x : P ≅ P')
    (y : R ≅ R') (s : P ≅ R) (q : P' ≅ R') (h : x.inv ≫ s.hom = q.hom ≫ y.inv) :
    s.inv ≫ x.hom = y.hom ≫ q.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  rw [Iso.inv_comp_eq] at h
  simp [h]

section Factors

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- The inverse of the derived square of exact functors on a localized complex, written with
the forward factorization maps. Source: Stacks 05S7
(blueprint: lem-pur-system-singleton-scalar-lower). -/
@[reassoc]
theorem Functor.mapDerivedCategorySquareIso_inv_app_factors (σ : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso σ).inv.app (DerivedCategory.Q.obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) =
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ.inv (.up ℤ)).app K) := by
  have h := iso_square_inv_inv
    (F₂.mapDerivedCategory.mapIso (F₁.mapDerivedCategoryFactors.app K) ≪≫
      F₂.mapDerivedCategoryFactors.app _)
    (G₂.mapDerivedCategory.mapIso (G₁.mapDerivedCategoryFactors.app K) ≪≫
      G₂.mapDerivedCategoryFactors.app _)
    ((Functor.mapDerivedCategorySquareIso σ).app _)
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex σ (.up ℤ)).app K))
    (Functor.mapDerivedCategorySquareIso_hom_app_inv_factors F₁ F₂ G₁ G₂ σ K)
  refine h.trans ?_
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rfl

end Factors

section Composition

variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (S : C ⥤ B) (R : B ⥤ A) (U : C ⥤ A)
  [S.Additive] [R.Additive] [U.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

/-- The exact restriction-composition comparison on a localized complex, inverse form.
Source: localization functoriality (blueprint: lem-pur-system-singleton-scalar-lower). -/
@[reassoc]
theorem Functor.exactDerivedRestrictionComposition_inv_app_factors (η : S ⋙ R ≅ U)
    (K : CochainComplex C ℤ) :
    (Functor.exactDerivedRestrictionComposition S R U η).inv.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) =
      U.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).inv.app K) := by
  have h := iso_square_inv_inv
    (R.mapDerivedCategory.mapIso (S.mapDerivedCategoryFactors.app K) ≪≫
      R.mapDerivedCategoryFactors.app _)
    (U.mapDerivedCategoryFactors.app K)
    ((Functor.exactDerivedRestrictionComposition S R U η).app _)
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex η (.up ℤ)).app K))
    (by
      refine Eq.trans ?_ (Functor.exactDerivedRestrictionComposition_inv_factors S R U η K)
      simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Category.assoc])
  refine h.trans ?_
  simp only [Iso.app_hom]
  rfl

end Composition

section TransitionSquare

variable {X Y Dm Dn Bm Bn : Type*} [Category X] [Category Y] [Category Dm] [Category Dn]
  [Category Bm] [Category Bn] [Abelian X] [Abelian Y] [Abelian Dm] [Abelian Dn]
  [Abelian Bm] [Abelian Bn] [HasDerivedCategory X] [HasDerivedCategory Y]
  [HasDerivedCategory Dm] [HasDerivedCategory Dn] [HasDerivedCategory Bm]
  [HasDerivedCategory Bn]
  {resA : X ⥤ Y} {evDm : X ⥤ Dm} {evDn : X ⥤ Dn} {evBm : Y ⥤ Bm} {evBn : Y ⥤ Bn}
  {resm : Dm ⥤ Bm} {resn : Dn ⥤ Bn} {ρD : Dn ⥤ Dm} {ρB : Bn ⥤ Bm} {rγ : Dn ⥤ Bm}
  [resA.Additive] [PreservesFiniteLimits resA] [PreservesFiniteColimits resA]
  [evDm.Additive] [PreservesFiniteLimits evDm] [PreservesFiniteColimits evDm]
  [evDn.Additive] [PreservesFiniteLimits evDn] [PreservesFiniteColimits evDn]
  [evBm.Additive] [PreservesFiniteLimits evBm] [PreservesFiniteColimits evBm]
  [evBn.Additive] [PreservesFiniteLimits evBn] [PreservesFiniteColimits evBn]
  [resm.Additive] [PreservesFiniteLimits resm] [PreservesFiniteColimits resm]
  [resn.Additive] [PreservesFiniteLimits resn] [PreservesFiniteColimits resn]
  [ρD.Additive] [PreservesFiniteLimits ρD] [PreservesFiniteColimits ρD]
  [ρB.Additive] [PreservesFiniteLimits ρB] [PreservesFiniteColimits ρB]
  [rγ.Additive] [PreservesFiniteLimits rγ] [PreservesFiniteColimits rγ]

/-- Localized transitions commute with derived squares of exact functors, provided that the
ordinary transitions commute with the ordinary squares. Source: functoriality of
localization, Stacks 05S7 (blueprint: lem-pur-system-singleton-scalar-lower).
Proof: both sides are natural, so it suffices to compare them on localized complexes. There
the factorization maps of the exact functors reduce both sides to the localized ordinary
maps, which agree degreewise. -/
theorem mapDerivedCategory_transition_square
    (tB : evBm.mapDerivedCategory ⟶ evBn.mapDerivedCategory ⋙ ρB.mapDerivedCategory)
    (τB : evBm ⟶ evBn ⋙ ρB)
    (htB : ∀ K : CochainComplex Y ℤ, tB.app (DerivedCategory.Q.obj K) ≫
      ρB.mapDerivedCategory.map (evBn.mapDerivedCategoryFactors.hom.app K) ≫
      ρB.mapDerivedCategoryFactors.hom.app ((evBn.mapHomologicalComplex (.up ℤ)).obj K) =
      evBm.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τB (.up ℤ)).app K))
    (tD : evDm.mapDerivedCategory ⟶ evDn.mapDerivedCategory ⋙ ρD.mapDerivedCategory)
    (τD : evDm ⟶ evDn ⋙ ρD)
    (htD : ∀ K : CochainComplex X ℤ, tD.app (DerivedCategory.Q.obj K) ≫
      ρD.mapDerivedCategory.map (evDn.mapDerivedCategoryFactors.hom.app K) ≫
      ρD.mapDerivedCategoryFactors.hom.app ((evDn.mapHomologicalComplex (.up ℤ)).obj K) =
      evDm.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τD (.up ℤ)).app K))
    (σm : resA ⋙ evBm ≅ evDm ⋙ resm) (σn : resA ⋙ evBn ≅ evDn ⋙ resn)
    (η₁ : resn ⋙ ρB ≅ rγ) (η₂ : ρD ⋙ resm ≅ rγ)
    (hord : ∀ M : X, σm.inv.app M ≫ τB.app (resA.obj M) =
      resm.map (τD.app M) ≫ η₂.hom.app (evDn.obj M) ≫ η₁.inv.app (evDn.obj M) ≫
        ρB.map (σn.inv.app M))
    (Y₀ : DerivedCategory X) :
    (Functor.mapDerivedCategorySquareIso σm).inv.app Y₀ ≫
        tB.app (resA.mapDerivedCategory.obj Y₀) =
      resm.mapDerivedCategory.map (tD.app Y₀) ≫
        (Functor.exactDerivedRestrictionComposition ρD resm rγ η₂).hom.app
          (evDn.mapDerivedCategory.obj Y₀) ≫
        (Functor.exactDerivedRestrictionComposition resn ρB rγ η₁).inv.app
          (evDn.mapDerivedCategory.obj Y₀) ≫
        ρB.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso σn).inv.app Y₀) := by
  have key (K : CochainComplex X ℤ) :
      (Functor.mapDerivedCategorySquareIso σm).inv.app (DerivedCategory.Q.obj K) ≫
        tB.app (resA.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) =
      resm.mapDerivedCategory.map (tD.app (DerivedCategory.Q.obj K)) ≫
        (Functor.exactDerivedRestrictionComposition ρD resm rγ η₂).hom.app
          (evDn.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        (Functor.exactDerivedRestrictionComposition resn ρB rγ η₁).inv.app
          (evDn.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        ρB.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso σn).inv.app
          (DerivedCategory.Q.obj K)) := by
    rw [← cancel_mono (ρB.mapDerivedCategory.map (evBn.mapDerivedCategory.map
        (resA.mapDerivedCategoryFactors.hom.app K)) ≫
      ρB.mapDerivedCategory.map (evBn.mapDerivedCategoryFactors.hom.app
        ((resA.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      ρB.mapDerivedCategoryFactors.hom.app ((evBn.mapHomologicalComplex (.up ℤ)).obj
        ((resA.mapHomologicalComplex (.up ℤ)).obj K)))]
    have nB := tB.naturality (resA.mapDerivedCategoryFactors.hom.app K)
    rw [Functor.comp_map] at nB
    have n1 := (Functor.exactDerivedRestrictionComposition resn ρB rγ η₁).inv.naturality
      (evDn.mapDerivedCategoryFactors.hom.app K)
    rw [Functor.comp_map] at n1
    have n2 := (Functor.exactDerivedRestrictionComposition ρD resm rγ η₂).hom.naturality
      (evDn.mapDerivedCategoryFactors.hom.app K)
    rw [Functor.comp_map] at n2
    have hσn := congrArg ρB.mapDerivedCategory.map
      (Functor.mapDerivedCategorySquareIso_inv_app_factors σn K)
    simp only [Functor.map_comp] at hσn
    have hD := congrArg resm.mapDerivedCategory.map (htD K)
    simp only [Functor.map_comp] at hD
    simp only [Category.assoc]
    rw [← reassoc_of% nB]
    erw [htB ((resA.mapHomologicalComplex (.up ℤ)).obj K)]
    rw [Functor.mapDerivedCategorySquareIso_inv_app_factors_assoc]
    rw [reassoc_of% hσn]
    erw [ρB.mapDerivedCategoryFactors_hom_naturality]
    rw [← reassoc_of% n1]
    erw [Functor.exactDerivedRestrictionComposition_inv_app_factors_assoc]
    rw [← reassoc_of% n2]
    erw [reassoc_of% (Functor.exactDerivedRestrictionComposition_hom_factors ρD resm rγ η₂
      ((evDn.mapHomologicalComplex (.up ℤ)).obj K))]
    rw [reassoc_of% hD]
    erw [resm.mapDerivedCategoryFactors_hom_naturality_assoc]
    congr 2
    simp only [← Functor.map_comp]
    congr 1
    ext i
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, NatIso.mapHomologicalComplex_hom_app_f,
      NatIso.mapHomologicalComplex_inv_app_f]
    exact hord (K.X i)
  have h : ((Functor.mapDerivedCategorySquareIso σm).inv ≫
      Functor.whiskerLeft resA.mapDerivedCategory tB :
        evDm.mapDerivedCategory ⋙ resm.mapDerivedCategory ⟶
          (resA.mapDerivedCategory ⋙ evBn.mapDerivedCategory) ⋙ ρB.mapDerivedCategory) =
      Functor.whiskerRight tD resm.mapDerivedCategory ≫
        Functor.whiskerLeft evDn.mapDerivedCategory
          (Functor.exactDerivedRestrictionComposition ρD resm rγ η₂).hom ≫
        Functor.whiskerLeft evDn.mapDerivedCategory
          (Functor.exactDerivedRestrictionComposition resn ρB rγ η₁).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso σn).inv
          ρB.mapDerivedCategory :=
    Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso X (.up ℤ)) key
  exact congr_app h Y₀

end TransitionSquare

end CategoryTheory
