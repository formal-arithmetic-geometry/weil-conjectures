/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
public import WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization

/-! # Formal properties of derived-limit pullback mates

General lemmas about mates of the derived constant/limit adjunctions of `DiagonalRlim`
with respect to exact functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section Mates

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ D} {H : E ⥤ F} {L₁ : C ⥤ E} {R₁ : E ⥤ C} {L₂ : D ⥤ F} {R₂ : F ⥤ D}

/-- A morphism composed with a mate is computed by transposing along the target adjunction. -/
theorem map_comp_mateEquiv_app_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    {c : C} {e : E} (f : c ⟶ R₁.obj e) (g : G.obj c ⟶ R₂.obj (H.obj e))
    (h : α.app c ≫ H.map (L₁.map f ≫ adj₁.counit.app e) =
      L₂.map g ≫ adj₂.counit.app (H.obj e)) :
    G.map f ≫ (mateEquiv adj₁ adj₂ α).app e = g := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, ← h, Functor.map_comp,
    Category.assoc, mateEquiv_counit, H.map_comp, ← Functor.comp_map, ← Functor.comp_map,
    α.naturality_assoc]

/-- Projections out of a mate: if both counits are computed by projections after
evaluation, and the square is compatible with evaluation, the mate commutes with the
projections. -/
theorem mateEquiv_app_comp_projection (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (V₁ : E ⥤ C) (V₂ : F ⥤ D) (e : H ⋙ V₂ ⟶ V₁ ⋙ G)
    (c₁ : L₁ ⋙ V₁ ⟶ 𝟭 C) (c₂ : L₂ ⋙ V₂ ≅ 𝟭 D) (π₁ : R₁ ⟶ V₁) (π₂ : R₂ ⟶ V₂)
    (h₁ : ∀ K, V₁.map (adj₁.counit.app K) = c₁.app (R₁.obj K) ≫ π₁.app K)
    (h₂ : ∀ K, V₂.map (adj₂.counit.app K) = c₂.hom.app (R₂.obj K) ≫ π₂.app K)
    (hα : ∀ Y, V₂.map (α.app Y) ≫ e.app (L₁.obj Y) ≫ G.map (c₁.app Y) = c₂.hom.app (G.obj Y))
    (K : E) :
    (mateEquiv adj₁ adj₂ α).app K ≫ π₂.app (H.obj K) ≫ e.app K = G.map (π₁.app K) := by
  have hπ : π₂.app (H.obj K) = c₂.inv.app _ ≫ V₂.map (adj₂.counit.app (H.obj K)) := by
    rw [h₂, Iso.inv_hom_id_app_assoc]
  have hc := c₂.inv.naturality ((mateEquiv adj₁ adj₂ α).app K)
  have he := e.naturality (adj₁.counit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hc he
  rw [hπ, Category.assoc, reassoc_of% hc, ← V₂.map_comp_assoc, mateEquiv_counit, V₂.map_comp,
    Category.assoc, he, h₁, G.map_comp, reassoc_of% hα, Iso.inv_hom_id_app_assoc]

end Mates

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

section Rlim

variable {A : Type a} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- The counit of a derived constant/limit adjunction is computed on every complex of towers
by the ordinary counit. -/
def DiagonalRlim.CounitFac (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R) : Prop :=
  ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app P) ≫
        adj.counit.app (DerivedCategory.Q.obj P) =
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.app P)

/-- The normalized counit equation of a derived constant/limit adjunction, known on
K-injective towers, holds on every complex of towers. -/
theorem DiagonalRlim.map_η_comp_counit (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R)
    (hres : ∀ K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (hcounit : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app I) ≫
          adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.app I)) :
    L.CounitFac adj := by
  intro P
  obtain ⟨I, q, hI, hq⟩ := hres P
  have hη : L.η.app P ≫ L.R.map (DerivedCategory.Q.map q) =
      DerivedCategory.Q.map (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).map q) ≫
        L.η.app I :=
    (L.η.naturality q).symm
  have hε := (Adjunction.mapHomologicalComplex (.up ℤ)
    (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.naturality q
  have hf := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.naturality
    (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).map q)
  dsimp only [Functor.comp_map, Functor.id_map] at hε hf
  rw [← cancel_mono (DerivedCategory.Q.map q), Category.assoc, ← adj.counit_naturality,
    ← Functor.map_comp_assoc, hη, Functor.map_comp, Category.assoc, hcounit I hI,
    ← Category.assoc, hf, Category.assoc, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, ← hε]

/-- The transpose of the cone map of an ordinary cone along a normalized derived
constant/limit adjunction is the cone itself, placed in degree zero. -/
@[reassoc]
theorem DiagonalRlim.map_coneMap_comp_counit (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R)
    (hcounit : L.CounitFac adj)
    (H : ℕᵒᵖ ⥤ A) (c : Cone H) :
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (diagonalTraceConeMap L H c) ≫
        adj.counit.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H) =
      ((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map c.π := by
  simp only [diagonalTraceConeMap, diagonalOrdinaryRlim, Functor.map_comp, Category.assoc]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [L.R.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [hcounit ((HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0).obj H)]
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  have hf := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.naturality
    ((HomologicalComplex.single A (.up ℤ) 0).map (limit.lift H c) ≫
      (HomologicalComplex.singleMapHomologicalComplex lim (.up ℤ) 0).inv.app H)
  dsimp only [Functor.comp_map] at hf
  rw [DerivedCategory.Q.map_comp, Functor.map_comp, Category.assoc] at hf
  erw [reassoc_of% hf]
  rw [Category.assoc]
  congr 1
  erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  ext n : 1
  by_cases hn : n = 0
  · subst hn
    ext j
    simp only [Functor.mapHomologicalComplex_obj_X, Functor.const_obj_obj, Functor.id_obj,
      Functor.map_comp, Category.assoc, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, lim_obj,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, lim_map,
      Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.comp_app, Functor.const_map_app,
      Functor.comp_obj, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, NatTrans.id_app,
      Category.id_comp]
    erw [Category.id_comp, Category.comp_id, Category.id_comp]
    rw [← lim_map]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact limit.lift_π c j
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_tgt _ _

end Rlim

end AlgebraicGeometry.ProEtale

namespace CategoryTheory

section ConstantPullback

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{u} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)]

/-- On objects placed in degree zero, the inverse of the canonical constant-tower
interchange is the identity-on-components comparison placed in degree zero. -/
@[reassoc]
theorem ringedConstantTowerPullback_inv_app_singleFunctor (M : B) :
    (ringedConstantTowerPullback F).inv.app ((DerivedCategory.singleFunctor B 0).obj M) ≫
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory.map
          (((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor 0).hom.app
          ((Functor.const ℕᵒᵖ).obj M) =
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        ((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategorySingleFunctor 0).hom.app
          (F.obj M) ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map
          ((Functor.compConstIso ℕᵒᵖ F).hom.app M) := by
  have he := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor
    (Functor.compConstIso ℕᵒᵖ F).symm M
  rw [
    ← Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app_assoc,
    ← Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app]
  simp only [ringedConstantTowerPullback, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  congr 1
  rw [← cancel_epi ((Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F).symm).hom.app
    ((DerivedCategory.singleFunctor B 0).obj M)), Iso.hom_inv_id_app_assoc, reassoc_of% he]
  simp

private theorem ringedConstantTowerPullback_inv_evaluation_Q (n : ℕᵒᵖ)
    (K : CochainComplex B ℤ) :
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
        ((ringedConstantTowerPullback F).inv.app (DerivedCategory.Q.obj K)) ≫
      (Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)
          ((evaluation ℕᵒᵖ A).obj n)).hom.app
        ((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      (Functor.mapDerivedCategoryCompIso ((evaluation ℕᵒᵖ B).obj n) F).inv.app
        ((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      F.mapDerivedCategory.map
        ((ringedConstantTowerEvaluation B n).hom.app (DerivedCategory.Q.obj K)) =
    (ringedConstantTowerEvaluation A n).hom.app
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := by
  let W := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let eA := (evaluation ℕᵒᵖ A).obj n
  let eB := (evaluation ℕᵒᵖ B).obj n
  let CB := (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B)
  let CA := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let e : W.mapDerivedCategory ⋙ eA.mapDerivedCategory ⟶
      eB.mapDerivedCategory ⋙ F.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso W eA).hom ≫ (Functor.mapDerivedCategoryCompIso eB F).inv
  have he (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
      e.app (DerivedCategory.Q.obj J) ≫ F.mapDerivedCategory.map
          (eB.mapDerivedCategoryFactors.hom.app J) ≫
        F.mapDerivedCategoryFactors.hom.app ((eB.mapHomologicalComplex (.up ℤ)).obj J) =
      eA.mapDerivedCategory.map (W.mapDerivedCategoryFactors.hom.app J) ≫
        eA.mapDerivedCategoryFactors.hom.app ((W.mapHomologicalComplex (.up ℤ)).obj J) := by
    simp only [e, NatTrans.comp_app, Category.assoc,
      Functor.mapDerivedCategoryCompIso_hom_app_factors,
      Functor.mapDerivedCategoryCompIso_hom_app_Q_obj,
      Functor.mapHomologicalComplexCompIso_refl_hom_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  have hE : (Functor.mapDerivedCategoryCompIso W eA).hom.app
        (CB.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      (Functor.mapDerivedCategoryCompIso eB F).inv.app
        (CB.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) =
      e.app (CB.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := rfl
  rw [reassoc_of% hE, ← cancel_mono (F.mapDerivedCategoryFactors.hom.app K)]
  have hR := (ringedConstantTowerEvaluation A n).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hR
  rw [← hR, ← rct_eval_fac A n ((F.mapHomologicalComplex _).obj K), ← rct_eval_fac B n K]
  have hn := e.naturality (CB.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  erw [he]
  have hp := rct_pull_fac F K
  have hp' : (ringedConstantTowerPullback F).inv.app (DerivedCategory.Q.obj K) ≫
      W.mapDerivedCategory.map (CB.mapDerivedCategoryFactors.hom.app K) ≫
        W.mapDerivedCategoryFactors.hom.app ((CB.mapHomologicalComplex (.up ℤ)).obj K) =
      CA.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        CA.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F) (.up ℤ)).hom.app K) := by
    rw [← cancel_epi ((ringedConstantTowerPullback F).hom.app (DerivedCategory.Q.obj K)),
      Iso.hom_inv_id_app_assoc, reassoc_of% hp, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id_app]
    erw [DerivedCategory.Q.map_id, Category.comp_id]
  have hq := eA.mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F) (.up ℤ)).hom.app K)
  have h1 : (eA.mapHomologicalComplex (.up ℤ)).map
      ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F) (.up ℤ)).hom.app K) = 𝟙 _ := by
    ext i
    simp [eA]
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [h1] at hq
  rw [← eA.mapDerivedCategory.map_comp_assoc, ← eA.mapDerivedCategory.map_comp_assoc,
    Category.assoc, hp',
    eA.mapDerivedCategory.map_comp, eA.mapDerivedCategory.map_comp, Category.assoc,
    Category.assoc]
  erw [hq, DerivedCategory.Q.map_id, Category.comp_id]
  rfl


/-- The inverse of the canonical constant-tower interchange is compatible with evaluation
at a level, the canonical evaluation comparison and the constant-tower evaluations. -/
theorem ringedConstantTowerPullback_inv_evaluation (n : ℕᵒᵖ) (Y : DerivedCategory B) :
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
        ((ringedConstantTowerPullback F).inv.app Y) ≫
      (Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)
          ((evaluation ℕᵒᵖ A).obj n)).hom.app
        ((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory.obj Y) ≫
      (Functor.mapDerivedCategoryCompIso ((evaluation ℕᵒᵖ B).obj n) F).inv.app
        ((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory.obj Y) ≫
      F.mapDerivedCategory.map ((ringedConstantTowerEvaluation B n).hom.app Y) =
    (ringedConstantTowerEvaluation A n).hom.app (F.mapDerivedCategory.obj Y) := by
  let W := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let eA := (evaluation ℕᵒᵖ A).obj n
  let eB := (evaluation ℕᵒᵖ B).obj n
  let CB := (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B)
  let CA := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let τ : F.mapDerivedCategory ⋙ CA.mapDerivedCategory ⋙ eA.mapDerivedCategory ⟶
      F.mapDerivedCategory :=
    Functor.whiskerRight (ringedConstantTowerPullback F).inv eA.mapDerivedCategory ≫
      Functor.whiskerLeft CB.mapDerivedCategory
        ((Functor.mapDerivedCategoryCompIso W eA).hom ≫
          (Functor.mapDerivedCategoryCompIso eB F).inv) ≫
      Functor.whiskerRight (ringedConstantTowerEvaluation B n).hom F.mapDerivedCategory
  let τ' : F.mapDerivedCategory ⋙ CA.mapDerivedCategory ⋙ eA.mapDerivedCategory ⟶
      F.mapDerivedCategory :=
    Functor.whiskerLeft F.mapDerivedCategory (ringedConstantTowerEvaluation A n).hom
  have h : τ = τ' := Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso B (.up ℤ))
    (fun K ↦ by
      simp only [τ, τ', NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Category.assoc]
      exact ringedConstantTowerPullback_inv_evaluation_Q F n K)
  simpa only [τ, τ', NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using congr_app h Y
end ConstantPullback

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

section PullbackMate

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{u} B] [Abelian A] [Abelian B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)]

/-- The mate of the canonical constant-tower interchange along two normalized derived
constant/limit adjunctions sends the derived cone map of an ordinary cone to the derived
cone map of its image. -/
theorem diagonalRlim_mate_coneMap (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (adjA : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ LA.R)
    (adjB : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ⊣ LB.R)
    (hA : LA.CounitFac adjA) (hB : LB.CounitFac adjB)
    (H : ℕᵒᵖ ⥤ B) (c : Cone H) :
    F.mapDerivedCategory.map (diagonalTraceConeMap LB H c) ≫
        (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _
          (ringedConstantTowerPullback F).inv)).app
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        LA.R.map ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor
          0).hom.app H) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
        diagonalTraceConeMap LA (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).obj H)
          (F.mapCone c) := by
  rw [← cancel_mono (LA.R.map
    ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor 0).inv.app H)),
    Category.assoc, Category.assoc, ← LA.R.map_comp, Iso.hom_inv_id_app]
  erw [LA.R.map_id, Category.comp_id]
  apply map_comp_mateEquiv_app_eq
  rw [DiagonalRlim.map_coneMap_comp_counit LB adjB hB H c]
  simp only [Functor.map_comp, Category.assoc]
  erw [adjA.counit_naturality]
  erw [DiagonalRlim.map_coneMap_comp_counit_assoc LA adjA hA]
  rw [← cancel_mono ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor
      0).hom.app H)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  have hn := (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor
    0).hom.naturality c.π
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]
  erw [ringedConstantTowerPullback_inv_app_singleFunctor_assoc F c.pt]
  congr 2
  rw [← Functor.map_comp]
  congr 1
  ext j
  simp


/-- The mate of the canonical constant-tower interchange along two derived constant/limit
adjunctions whose counits are computed by the level projections commutes with the level
projections. -/
theorem diagonalRlim_mate_projection (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (adjA : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ LA.R)
    (adjB : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ⊣ LB.R)
    (hA : ∀ (n : ℕ) (K : DerivedCategory (ℕᵒᵖ ⥤ A)),
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map (adjA.counit.app K) =
        (ringedConstantTowerEvaluation A (op n)).hom.app (LA.R.obj K) ≫
          (LA.projection n).app K)
    (hB : ∀ (n : ℕ) (K : DerivedCategory (ℕᵒᵖ ⥤ B)),
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (adjB.counit.app K) =
        (ringedConstantTowerEvaluation B (op n)).hom.app (LB.R.obj K) ≫
          (LB.projection n).app K)
    (n : ℕ) (K : DerivedCategory (ℕᵒᵖ ⥤ B)) :
    (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ (ringedConstantTowerPullback F).inv)).app K ≫
        (LA.projection n).app
          (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory.obj K) ≫
        (Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)
            ((evaluation ℕᵒᵖ A).obj (op n)) ≪≫
          Functor.mapDerivedCategoryNatIso (eqToIso rfl) ≪≫
          (Functor.mapDerivedCategoryCompIso ((evaluation ℕᵒᵖ B).obj (op n)) F).symm).hom.app K =
      F.mapDerivedCategory.map ((LB.projection n).app K) := by
  refine mateEquiv_app_comp_projection adjB adjA _ _ _ _
    (ringedConstantTowerEvaluation B (op n)).hom (ringedConstantTowerEvaluation A (op n))
    (LB.projection n) (LA.projection n) (hB n) (hA n) (fun Y ↦ ?_) K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso_refl,
    Functor.mapDerivedCategoryNatIso_refl, Category.id_comp, Category.assoc]
  exact ringedConstantTowerPullback_inv_evaluation F (op n) Y

/-- The mate of the canonical constant-tower interchange sends the derived comparison of an
exact scalar cone to the derived comparison of the pulled-back cone. -/
theorem diagonalRlim_mate_exactConeComparison {C : Type*} {D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (U : C ⥤ B) (V : D ⥤ (ℕᵒᵖ ⥤ B)) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (adjA : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ LA.R)
    (adjB : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ⊣ LB.R)
    (hcone : ∀ (H : ℕᵒᵖ ⥤ B) (c : Cone H),
      F.mapDerivedCategory.map (diagonalTraceConeMap LB H c) ≫
          (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _
            (ringedConstantTowerPullback F).inv)).app
            ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
          LA.R.map ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor
            0).hom.app H) =
        (F.mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
          diagonalTraceConeMap LA (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).obj H)
            (F.mapCone c))
    (M : C) (N : D) (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N) :
    F.mapDerivedCategory.map (exactConeComparison U V LB M N π) ≫
        (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ (ringedConstantTowerPullback F).inv)).app
          (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor D 0).obj N)) =
      (Functor.mapDerivedCategoryCompIso U F).hom.app
          ((DerivedCategory.singleFunctor C 0).obj M) ≫
        exactConeComparison (U ⋙ F) (V ⋙ (Functor.whiskeringRight ℕᵒᵖ B A).obj F) LA M N
          ((Functor.compConstIso ℕᵒᵖ F).hom.app (U.obj M) ≫
            ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).map π) ≫
        LA.R.map ((Functor.mapDerivedCategoryCompIso V
          ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)).inv.app
            ((DerivedCategory.singleFunctor D 0).obj N)) := by
  let W := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  set β := mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ (ringedConstantTowerPullback F).inv)
  let c : Cone (V.obj N) := ⟨U.obj M, π⟩
  have hc := hcone (V.obj N) c
  have hc' : F.mapDerivedCategory.map (diagonalTraceConeMap LB (V.obj N) c) ≫
      β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (V.obj N)) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
        diagonalTraceConeMap LA (W.obj (V.obj N)) (F.mapCone c) ≫
        LA.R.map ((W.mapDerivedCategorySingleFunctor 0).inv.app (V.obj N)) := by
    rw [← reassoc_of% hc, ← LA.R.map_comp, Iso.hom_inv_id_app]
    erw [LA.R.map_id, Category.comp_id]
  have hn := β.naturality ((V.mapDerivedCategorySingleFunctor 0).inv.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hlift : limit.lift (W.obj (V.obj N)) (F.mapCone c) =
      limit.lift ((V ⋙ W).obj N)
        ⟨(U ⋙ F).obj M, (Functor.compConstIso ℕᵒᵖ F).hom.app (U.obj M) ≫ W.map π⟩ := by
    apply limit.hom_ext
    intro j
    simp [c, W]
  have hV := Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app
    V W N 0
  simp only [exactConeComparison, Functor.map_comp, Category.assoc]
  have hcm : F.mapDerivedCategory.map ((DerivedCategory.singleFunctor B 0).map
        (limit.lift (V.obj N) c)) ≫ F.mapDerivedCategory.map (diagonalOrdinaryRlim LB (V.obj N)) =
      F.mapDerivedCategory.map (diagonalTraceConeMap LB (V.obj N) c) :=
    (F.mapDerivedCategory.map_comp _ _).symm
  have hV' : ((V ⋙ W).mapDerivedCategorySingleFunctor 0).inv.app N ≫
      (Functor.mapDerivedCategoryCompIso V W).inv.app
        ((DerivedCategory.singleFunctor D 0).obj N) =
      (W.mapDerivedCategorySingleFunctor 0).inv.app (V.obj N) ≫
        W.mapDerivedCategory.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N) := by
    rw [← cancel_epi (((V ⋙ W).mapDerivedCategorySingleFunctor 0).hom.app N),
      Iso.hom_inv_id_app_assoc, ← cancel_epi ((Functor.mapDerivedCategoryCompIso V W).hom.app
        ((DerivedCategory.singleFunctor D 0).obj N)), Iso.hom_inv_id_app, reassoc_of% hV,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    rfl
  rw [hn, reassoc_of% hcm, reassoc_of% hc',
    Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app_assoc]
  congr 2
  simp only [diagonalTraceConeMap, Category.assoc]
  erw [hlift]
  congr 2
  rw [← LA.R.map_comp, ← LA.R.map_comp, hV']

/-- The mate of the canonical constant-tower interchange is invertible on a tower placed in
degree zero, as soon as the ordinary-to-derived limit comparisons of the tower and of its
image are invertible and the exact functor preserves the limit of the tower. -/
theorem diagonalRlim_mate_app_isIso (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (adjA : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ LA.R)
    (adjB : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ⊣ LB.R)
    (hcone : ∀ (H : ℕᵒᵖ ⥤ B) (c : Cone H),
      F.mapDerivedCategory.map (diagonalTraceConeMap LB H c) ≫
          (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _
            (ringedConstantTowerPullback F).inv)).app
            ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
          LA.R.map ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor
            0).hom.app H) =
        (F.mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
          diagonalTraceConeMap LA (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).obj H)
            (F.mapCone c))
    (H : ℕᵒᵖ ⥤ B) (hB : IsIso (diagonalOrdinaryRlim LB H))
    (hA : IsIso (diagonalOrdinaryRlim LA (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).obj H)))
    (hF : IsIso (limit.post H F)) :
    IsIso ((mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ (ringedConstantTowerPullback F).inv)).app
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)) := by
  have h := hcone H (limit.cone H)
  have h₁ : IsIso (diagonalTraceConeMap LB H (limit.cone H)) := by
    rw [diagonalTraceConeMap, limit.lift_cone]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact hB
  have h₂ : IsIso (diagonalTraceConeMap LA (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).obj H)
      (F.mapCone (limit.cone H))) := by
    have : IsIso (limit.lift (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).obj H)
        (F.mapCone (limit.cone H))) := hF
    rw [diagonalTraceConeMap]
    infer_instance
  rw [← IsIso.eq_inv_comp] at h
  have : IsIso ((mateEquiv adjB adjA (TwoSquare.mk _ _ _ _
      (ringedConstantTowerPullback F).inv)).app
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
      LA.R.map ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor
        0).hom.app H)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (LA.R.map ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategorySingleFunctor
      0).hom.app H))
end PullbackMate

end AlgebraicGeometry.ProEtale

namespace CategoryTheory

/-- Every complex of strict towers in a Grothendieck abelian category has a K-injective
resolution. -/
theorem exists_isKInjective_tower (A : Type a) [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q := by
  let := isGrothendieckAbelian_tower.{a, v, v} A
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  exact ⟨I, q, hI, hq⟩

end CategoryTheory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [F.CommShift A] [G.CommShift A]

set_option backward.defeqAttrib.useBackward true in
/-- An adjunction between functors commuting with shifts is compatible with the shifts as soon
as its counit commutes with the shifts. -/
lemma commShift_of_counit (h : NatTrans.CommShift adj.counit A) : adj.CommShift A := by
  refine CommShift.mk' adj A ⟨fun a ↦ ?_⟩
  have hc : CommShift.CompatibilityCounit adj (F.commShiftIso a) (G.commShiftIso a) := by
    intro Y
    simpa [Functor.commShiftIso_comp_hom_app] using (NatTrans.shift_app_comm adj.counit a Y).symm
  ext X
  simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
    Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_id_hom_app, Category.id_comp]
  rw [CommShift.compatibilityCounit_left adj _ _ hc X]
  simp

end CategoryTheory.Adjunction


namespace CategoryTheory.NatTrans.CommShift

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A]

/-- A natural transformation commutes with shifts if, after precomposition with a functor
commuting with shifts that reaches every object up to isomorphism, it is the quotient of a
natural transformation commuting with shifts by an isomorphism commuting with shifts. -/
lemma of_isIso_comp_whiskerLeft {F₁ F₂ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.CommShift A]
    [F₂.CommShift A] (L : E ⥤ C) [L.CommShift A] {G : E ⥤ D} [G.CommShift A]
    (θ : G ⟶ L ⋙ F₁) (ψ : G ⟶ L ⋙ F₂) [IsIso θ] [NatTrans.CommShift θ A]
    [NatTrans.CommShift ψ A] (hψ : θ ≫ Functor.whiskerLeft L τ = ψ)
    (h : ∀ X, ∃ (Y : E) (f : X ⟶ L.obj Y), IsIso (F₂.map f)) : NatTrans.CommShift τ A := by
  have := NatTrans.CommShift.of_isIso θ A
  have : NatTrans.CommShift (Functor.whiskerLeft L τ) A := by
    rw [← IsIso.eq_inv_comp] at hψ
    rw [hψ]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft τ L h

end CategoryTheory.NatTrans.CommShift
namespace AlgebraicGeometry.ProEtale

section CommShift

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{u} B] [Abelian A] [Abelian B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

/-- The counit of a derived constant/limit adjunction computed by the ordinary counit commutes
with the shifts. -/
theorem DiagonalRlim.counit_commShift (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R)
    (hres : ∀ K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (hcounit : L.CounitFac adj) :
    NatTrans.CommShift adj.counit ℤ := by
  let P : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ A) ℤ) := fun I ↦ I.IsKInjective
  have : P.IsStableUnderShift ℤ := ⟨fun a ↦ ⟨fun I (hI : I.IsKInjective) ↦
    (inferInstance : (I⟦a⟧).IsKInjective)⟩⟩
  let Cd := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory
  let lh := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)
  let ch := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)
  let adjh := Adjunction.mapHomologicalComplex (.up ℤ)
    (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)
  let θ : P.ι ⋙ ((lh ⋙ DerivedCategory.Q) ⋙ Cd) ⟶
      (P.ι ⋙ DerivedCategory.Q) ⋙ (L.R ⋙ Cd) :=
    Functor.whiskerLeft P.ι (Functor.whiskerRight L.η Cd) ≫
      Functor.whiskerLeft P.ι (Functor.associator DerivedCategory.Q L.R Cd).hom ≫
      (Functor.associator P.ι DerivedCategory.Q (L.R ⋙ Cd)).inv
  let ψ : P.ι ⋙ ((lh ⋙ DerivedCategory.Q) ⋙ Cd) ⟶ (P.ι ⋙ DerivedCategory.Q) ⋙ 𝟭 _ :=
    Functor.whiskerLeft P.ι ((Functor.associator lh DerivedCategory.Q Cd).hom ≫
      Functor.whiskerLeft lh
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom ≫
      (Functor.associator lh ch DerivedCategory.Q).inv ≫
      Functor.whiskerRight adjh.counit DerivedCategory.Q ≫
      DerivedCategory.Q.leftUnitor.hom ≫ DerivedCategory.Q.rightUnitor.inv) ≫
    (Functor.associator P.ι DerivedCategory.Q (𝟭 _)).inv
  have : IsIso θ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro I
    have := L.computation I.obj I.property
    simp only [θ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id]
    erw [Category.comp_id]
    exact (inferInstance : IsIso (Cd.map (L.η.app I.obj)))
  refine NatTrans.CommShift.of_isIso_comp_whiskerLeft adj.counit
    (P.ι ⋙ DerivedCategory.Q) θ ψ ?_ ?_
  · ext I
    simp only [θ, ψ, Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    erw [Category.id_comp]
    exact hcounit I.obj
  · intro K
    obtain ⟨I, q, hI, hq⟩ := hres (DerivedCategory.Q.objPreimage K)
    exact ⟨⟨I, hI⟩, (DerivedCategory.Q.objObjPreimageIso K).inv ≫ DerivedCategory.Q.map q,
      inferInstanceAs (IsIso ((DerivedCategory.Q.objObjPreimageIso K).inv ≫
        DerivedCategory.Q.map q))⟩

variable (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)]

omit [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)] in
/-- The mate of the canonical constant-tower interchange along two derived constant/limit
adjunctions compatible with the shifts commutes with the shifts. -/
theorem diagonalRlim_mate_commShift (LA : DiagonalRlim A) (LB : DiagonalRlim B)
    (adjA : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ LA.R)
    (adjB : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ⊣ LB.R)
    (hA : NatTrans.CommShift adjA.counit ℤ) (hB : NatTrans.CommShift adjB.counit ℤ) :
    NatTrans.CommShift
      (mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ (ringedConstantTowerPullback F).inv)) ℤ := by
  have := adjA.commShift_of_counit ℤ hA
  have := adjB.commShift_of_counit ℤ hB
  have : NatTrans.CommShift (ringedConstantTowerPullback F).inv ℤ := by
    simp only [ringedConstantTowerPullback, Iso.trans_inv, Iso.symm_inv]
    infer_instance
  exact NatTrans.CommShift.mateEquiv adjB adjA _

end CommShift

end AlgebraicGeometry.ProEtale
