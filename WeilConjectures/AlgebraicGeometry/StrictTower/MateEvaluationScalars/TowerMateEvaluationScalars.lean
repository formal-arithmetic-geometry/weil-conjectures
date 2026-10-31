/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenScalars.FiniteOpenExchangeScalars
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport

/-! # Evaluation and scalar restriction of the clopen proper/open mate

Source: Stacks Project, sites-cohomology.tex, Tags 07A7 and 0D6E;
sites-modules.tex, Tags 03DI and 03DJ, and the strict-tower refinement
(blueprint: lem-cbc-tower-mate-evaluation-scalars).

The single-level arrow is the exact descent of the existing ordinary clopen arrow.
All comparison maps are constructed from the specified adjunctions. Index `n` means
positive level `n+1`; no boundedness, flatness or finite-coefficient assumption occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars

section ExactTransformations
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D H : Type*} [Category C] [Category D] [Category H]
  [Abelian C] [Abelian D] [Abelian H]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
  {F G : C ⥤ D}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private def exactNat (t : F ⟶ G) : F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q)

@[reassoc] private theorem exactNat_fac (t : F ⟶ G) (K : CochainComplex C ℤ) :
    (exactNat t).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory =
      F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) G.mapDerivedCategory =
      G.mapDerivedCategoryFactors := rfl
  simp only [exactNat, Localization.liftNatTrans_app, hF, hG, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, Functor.whiskerRight_app]

private theorem derived_refl_iso :
    Functor.mapDerivedCategoryNatIso (Iso.refl F) = Iso.refl _ := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem exactNat_comp (t : F ⟶ G) {J : C ⥤ D}
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J] (s : G ⟶ J) :
    exactNat (t ≫ s) = exactNat t ≫ exactNat s := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (J.mapDerivedCategoryFactors.hom.app K)).1
  simp only [NatTrans.comp_app, Category.assoc, exactNat_fac,
    exactNat_fac_assoc, NatTrans.mapHomologicalComplex_comp, Functor.map_comp]

private theorem exactNat_iso (e : F ≅ G) :
    exactNat e.hom = (Functor.mapDerivedCategoryNatIso e).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app K)).1
  rw [exactNat_fac, Functor.mapDerivedCategoryNatIso_fac]

private theorem exactNat_whiskerRight (t : F ⟶ G) (K : D ⥤ H)
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K] :
    exactNat (Functor.whiskerRight t K) ≫ (Functor.mapDerivedCategoryCompIso G K).hom =
      (Functor.mapDerivedCategoryCompIso F K).hom ≫
        Functor.whiskerRight (exactNat t) K.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (fun L ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← cancel_mono (K.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app L) ≫
      K.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj L)),
    Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors, exactNat_fac,
    Category.assoc, ← Functor.map_comp_assoc, exactNat_fac, Functor.map_comp_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

private theorem exactNat_whiskerLeft (K : H ⥤ C)
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K] (t : F ⟶ G) :
    exactNat (Functor.whiskerLeft K t) ≫ (Functor.mapDerivedCategoryCompIso K G).hom =
      (Functor.mapDerivedCategoryCompIso K F).hom ≫
        Functor.whiskerLeft K.mapDerivedCategory (exactNat t) := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso H (.up ℤ)) (fun L ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (G.mapDerivedCategory.map (K.mapDerivedCategoryFactors.hom.app L) ≫
      G.mapDerivedCategoryFactors.hom.app ((K.mapHomologicalComplex (.up ℤ)).obj L)),
    Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors, exactNat_fac,
    Category.assoc, ← reassoc_of% ((exactNat t).naturality
      (K.mapDerivedCategoryFactors.hom.app L)), exactNat_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

private theorem exactNat_square
    {C' D' : Type*} [Category C'] [Category D'] [Abelian C'] [Abelian D']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    {F' G' : C' ⥤ D'}
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (u : C ⥤ C') (v : D ⥤ D')
    [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (p : F ⋙ v ≅ u ⋙ F') (q : G ⋙ v ≅ u ⋙ G') (t : F ⟶ G) (t' : F' ⟶ G')
    (h : Functor.whiskerRight t v ≫ q.hom = p.hom ≫ Functor.whiskerLeft u t') :
    Functor.whiskerRight (exactNat t) v.mapDerivedCategory ≫
        (Functor.mapDerivedCategorySquareIso q).hom =
      (Functor.mapDerivedCategorySquareIso p).hom ≫
        Functor.whiskerLeft u.mapDerivedCategory (exactNat t') := by
  have hm : exactNat (Functor.whiskerRight t v) ≫
      (Functor.mapDerivedCategoryNatIso q).hom =
      (Functor.mapDerivedCategoryNatIso p).hom ≫
        exactNat (Functor.whiskerLeft u t') := by
    rw [← exactNat_iso, ← exactNat_iso, ← exactNat_comp, ← exactNat_comp, h]
  have hR := exactNat_whiskerRight t v
  have hL := exactNat_whiskerLeft u t'
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso F v).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hR, Iso.hom_inv_id_assoc, reassoc_of% hm, hL]

private theorem exactNat_unique (t : F ⟶ G) (δ : F.mapDerivedCategory ⟶ G.mapDerivedCategory)
    (h : ClopenProjectorDescent F G t δ) : δ = exactNat t := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app K)).1
  rw [exactNat_fac]
  exact h K

variable [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]

private theorem evalD_trans (t : F ⟶ G) (n : ℕ) :
    Functor.whiskerRight
        (exactNat ((Functor.whiskeringRight ℕᵒᵖ C D).map t))
        (E D n).mapDerivedCategory ≫ (evalD G n).hom =
      (evalD F n).hom ≫ Functor.whiskerLeft (E C n).mapDerivedCategory
        (exactNat t) := by
  have h₁ := exactNat_whiskerRight
    ((Functor.whiskeringRight ℕᵒᵖ C D).map t) (E D n)
  have h₂ := exactNat_whiskerLeft (E C n) t
  have he : Functor.whiskerRight ((Functor.whiskeringRight ℕᵒᵖ C D).map t) (E D n) =
      Functor.whiskerLeft (E C n) t := rfl
  rw [he] at h₁
  dsimp only [evalD, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso (W F) (E D n)).hom]
  simp only [Category.assoc]
  rw [← reassoc_of% h₁, Iso.hom_inv_id_assoc]
  rw [Iso.hom_inv_id_assoc]
  exact h₂

private def exactSquare
    {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
    [HasDerivedCategory A] [HasDerivedCategory A']
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F₁ F₂).inv ≫ exactNat t ≫
    (Functor.mapDerivedCategoryCompIso G₁ G₂).hom

private theorem evalD_square_trans
    {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
    [HasDerivedCategory A] [HasDerivedCategory A']
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ A')]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) (M : DerivedCategory (ℕᵒᵖ ⥤ C)) (n : ℕ) :
    (E D n).mapDerivedCategory.map
        ((exactSquare (W F₁) (W F₂) (W G₁) (W G₂)
          (Functor.termwiseCompositeTransformation ℕᵒᵖ C A A' D F₁ F₂ G₁ G₂ t)).app M) ≫
      (evalD G₂ n).hom.app ((W G₁).mapDerivedCategory.obj M) ≫
      G₂.mapDerivedCategory.map ((evalD G₁ n).hom.app M) =
    (evalD F₂ n).hom.app ((W F₁).mapDerivedCategory.obj M) ≫
      F₂.mapDerivedCategory.map ((evalD F₁ n).hom.app M) ≫
      (exactSquare F₁ F₂ G₁ G₂ t).app ((E C n).mapDerivedCategory.obj M) := by
  have ht : Functor.termwiseCompositeTransformation ℕᵒᵖ C A A' D F₁ F₂ G₁ G₂ t =
      (Functor.whiskeringRight ℕᵒᵖ C D).map t := by
    ext L m
    simp [Functor.termwiseCompositeTransformation, Functor.whiskeringRightObjCompIso]
  rw [ht]
  have hF := congrArg (fun z ↦ z.app M) (evalD_comp F₁ F₂ n)
  have hG := congrArg (fun z ↦ z.app M) (evalD_comp G₁ G₂ n)
  have he := congrArg (fun z ↦ z.app M) (evalD_trans t n)
  dsimp only [exactSquare, NatTrans.comp_app] at *
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app] at hF hG he
  rw [← cancel_epi ((E D n).mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso (W F₁) (W F₂)).hom.app M))]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, hG, reassoc_of% he, reassoc_of% hF]
  simp only [Iso.hom_inv_id_app_assoc]

omit [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)] in
private theorem exactSquare_unique
    {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
    [HasDerivedCategory A] [HasDerivedCategory A']
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂)
    (a : F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory)
    (h : ClopenProjectorDescent (F₁ ⋙ F₂) (G₁ ⋙ G₂) t
      ((Functor.mapDerivedCategoryCompIso F₁ F₂).hom ≫ a ≫
        (Functor.mapDerivedCategoryCompIso G₁ G₂).inv)) :
    a = exactSquare F₁ F₂ G₁ G₂ t := by
  have he := exactNat_unique t _ h
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso F₁ F₂).hom,
    ← cancel_mono (Functor.mapDerivedCategoryCompIso G₁ G₂).inv]
  simpa only [exactSquare, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using he

end ExactTransformations

section ExactEvaluation
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
  {L : C ⥤ D} {R : D ⥤ C}
  [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private theorem exact_evaluation_unit (a : L ⊣ R) (n : ℕ)
    (M : DerivedCategory (ℕᵒᵖ ⥤ C)) :
    (E C n).mapDerivedCategory.map ((exactAdj (a.whiskerRight ℕᵒᵖ)).unit.app M) ≫
        (evalD R n).hom.app ((W L).mapDerivedCategory.obj M) =
      (exactAdj a).unit.app ((E C n).mapDerivedCategory.obj M) ≫
        R.mapDerivedCategory.map ((evalD L n).inv.app M) := by
  have hu := exact_mate (u := E C n) (v := E D n)
    (a.whiskerRight ℕᵒᵖ) a (Iso.refl _) (Iso.refl _)
    (exactAdj (a.whiskerRight ℕᵒᵖ)) (exactAdj a)
    (exactAdj_unit _) (exactAdj_unit _)
    (by
      intro K
      dsimp only [E, W, evaluation, Functor.whiskeringRight]
      simp only [Iso.refl_hom, NatTrans.id_app, Adjunction.whiskerRight_unit_app_app]
      dsimp only [Functor.comp_obj]
      simp only [CategoryTheory.Functor.map_id, Category.comp_id]) M
  simpa only [Functor.mapDerivedCategorySquareIso, evalD, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, derived_refl_iso, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id, Category.assoc] using hu.symm

omit [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_resolution_normalized (a : L ⊣ R) (n : ℕ)
    (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    (E C n).mapDerivedCategoryFactors.inv.app
        (((W R).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (E C n).mapDerivedCategory.map (chainDerivedUnit (W R) I) ≫
      (mateEquiv (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
        a.mapDerivedCategoryRightDerivedAdjunction (evalD L n).inv).app
          (DerivedCategory.Q.obj I) ≫
      R.rightDerivedFunctor.map ((E D n).mapDerivedCategoryFactors.hom.app I) =
        chainDerivedUnit R (((E D n).mapHomologicalComplex (.up ℤ)).obj I) := by
  let s : E C n ⋙ L ≅ W L ⋙ E D n := Iso.refl _
  have hm : (mateEquiv (a.whiskerRight ℕᵒᵖ) a
      (TwoSquare.mk _ _ _ _ s.hom)).natTrans = 𝟙 (E D n ⋙ R) := by
    ext T
    simp only [s, Iso.refl_hom, mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk,
      TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.rightUnitor_inv_app,
      Functor.leftUnitor_hom_app, Category.id_comp,
      Functor.comp_obj, Functor.comp_map, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
    change a.unit.app (R.obj (T.obj (op n))) ≫
      R.map (((a.whiskerRight ℕᵒᵖ).counit.app T).app (op n)) ≫ 𝟙 _ = 𝟙 _
    rw [Adjunction.whiskerRight_counit_app_app, Category.comp_id]
    exact a.right_triangle_components _
  have hs : ((Functor.mapDerivedCategoryCompIso (E C n) L).symm ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫
      Functor.mapDerivedCategoryCompIso (W L) (E D n)).hom =
        (evalD L n).inv := by
    simp only [s, derived_refl_iso, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
      Category.id_comp, evalD, Iso.trans_inv, Iso.symm_inv]
  have hf := _root_.derived_mate_factors (a.whiskerRight ℕᵒᵖ) a s I
  rw [hs, hm] at hf
  have hid : (NatTrans.mapHomologicalComplex (𝟙 (E D n ⋙ R)) (.up ℤ)).app I =
      𝟙 _ := by ext z; rfl
  erw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at hf
  rw [hf, Iso.inv_hom_id_app_assoc]

end ExactEvaluation

section ExactScalarDescent
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exactSquare_scalar
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    {F : A ⥤ B} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D}
    {F' : A' ⥤ B'} {G' : A' ⥤ C'} {H' : B' ⥤ D'} {K' : C' ⥤ D'}
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [F'.Additive] [G'.Additive] [H'.Additive] [K'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    (u₀ : A ⥤ A') (u₁ : B ⥤ B') (u₂ : C ⥤ C') (u₃ : D ⥤ D')
    [u₀.Additive] [u₁.Additive] [u₂.Additive] [u₃.Additive]
    [PreservesFiniteLimits u₀] [PreservesFiniteColimits u₀]
    [PreservesFiniteLimits u₁] [PreservesFiniteColimits u₁]
    [PreservesFiniteLimits u₂] [PreservesFiniteColimits u₂]
    [PreservesFiniteLimits u₃] [PreservesFiniteColimits u₃]
    (pF : F ⋙ u₁ ≅ u₀ ⋙ F') (pG : G ⋙ u₂ ≅ u₀ ⋙ G')
    (pH : H ⋙ u₃ ≅ u₁ ⋙ H') (pK : K ⋙ u₃ ≅ u₂ ⋙ K')
    (t : G ⋙ K ⟶ F ⋙ H) (t' : G' ⋙ K' ⟶ F' ⋙ H')
    (h : ∀ L, u₃.map (t.app L) ≫ pH.hom.app (F.obj L) ≫ H'.map (pF.hom.app L) =
      pK.hom.app (G.obj L) ≫ K'.map (pG.hom.app L) ≫ t'.app (u₀.obj L))
    (M : DerivedCategory A) :
    u₃.mapDerivedCategory.map ((exactSquare G K F H t).app M) ≫
        (Functor.mapDerivedCategorySquareIso pH).hom.app (F.mapDerivedCategory.obj M) ≫
        H'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso pF).hom.app M) =
      (Functor.mapDerivedCategorySquareIso pK).hom.app (G.mapDerivedCategory.obj M) ≫
        K'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso pG).hom.app M) ≫
        (exactSquare G' K' F' H' t').app (u₀.mapDerivedCategory.obj M) := by
  let a := Functor.associator G K u₃ ≪≫
    Functor.isoWhiskerLeft G pK ≪≫
    (Functor.associator G u₂ K').symm ≪≫
    Functor.isoWhiskerRight pG K' ≪≫
    Functor.associator u₀ G' K'
  let b := Functor.associator F H u₃ ≪≫
    Functor.isoWhiskerLeft F pH ≪≫
    (Functor.associator F u₁ H').symm ≪≫
    Functor.isoWhiskerRight pF H' ≪≫
    Functor.associator u₀ F' H'
  have hc : Functor.whiskerRight t u₃ ≫ b.hom =
      a.hom ≫ Functor.whiskerLeft u₀ t' := by
    apply NatTrans.ext
    funext L
    simpa only [a, b, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
      using h L
  have hd := congrArg (fun z ↦ z.app M)
    (exactNat_square u₀ u₃ a b
      t t' hc)
  have ha := Functor.exactSquare_comp_forward G K
    (G ⋙ K) G' K'
    (G' ⋙ K') u₀ u₂
    u₃ pG pK a (Iso.refl _) (Iso.refl _)
    (by intro L; simp [a]) M
  have hb := Functor.exactSquare_comp_forward F H
    (F ⋙ H) F' H'
    (F' ⋙ H') u₀ u₁
    u₃ pF pH b (Iso.refl _) (Iso.refl _)
    (by intro L; simp [b]) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_refl,
    Category.id_comp] at ha hb
  rw [← cancel_epi (u₃.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso G K).hom.app M))]
  simp only [exactSquare, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Category.assoc, Iso.symm_hom] at ha hb
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hd
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at hd ⊢
  rw [hb, reassoc_of% hd]
  have he := congrArg (fun z ↦ z ≫
    (Functor.mapDerivedCategoryCompIso G' K').inv.app
      (u₀.mapDerivedCategory.obj M) ≫
    (exactNat t').app (u₀.mapDerivedCategory.obj M) ≫
    (Functor.mapDerivedCategoryCompIso F' H').hom.app
      (u₀.mapDerivedCategory.obj M)) ha
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at he
  exact he.symm

end ExactScalarDescent

variable (B : Type (u + 1)) [CommRing B]

/-- Existing sheafification at the actual coefficient universe of the small site.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance siteSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

/-- The existing local-bijection characterization at the same coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance siteLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

/-- The existing abelian structure with its coefficient universe made explicit.
Source: Stacks 03DA (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance modulesAbelian (X : Scheme.{u}) : Abelian (Modules B X) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
    (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
    (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1})

/-- The existing single-level exact inverse image, abbreviated for the formulas below.
Source: Stacks 03EK, 07A6 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev g {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules B Y) ⥤ DerivedCategory (Modules B X) :=
  (modulePullback B f).mapDerivedCategory

/-- The existing single-level total direct image.
Source: Stacks 07A5 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev r {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules B X) ⥤ DerivedCategory (Modules B Y) :=
  (moduleDirectImage B f).rightDerivedFunctor

/-- Exact descent of the existing single-level extension by zero.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev j {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    DerivedCategory (Modules B U) ⥤ DerivedCategory (Modules B X) :=
  (moduleJ B f).mapDerivedCategory

/-- The specified single-level derived adjunction.
Source: Stacks 07A6 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev dAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : g B f ⊣ r B f :=
  (clopenModuleAdj B f).mapDerivedCategoryRightDerivedAdjunction

/-- The exact single-level open adjunction, with its original unit and counit.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def dJAdj {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] : j B f ⊣ g B f :=
  (moduleJAdj B f).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (modulePullback B f).rightDerivedFunctorIsoMapDerivedCategory

private theorem exactAdj_dJAdj {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] : exactAdj (moduleJAdj B f) = dJAdj B f := by
  unfold exactAdj dJAdj
  rfl

/-- Exact descent of the specified ordinary alpha, with both composition factors.
Source: Stacks 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def singleDerivedAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) : j B i ⋙ g B p ⟶ g B f ⋙ j B k :=
  (Functor.mapDerivedCategoryCompIso _ _).inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules B S) (.up ℤ))
      ((moduleJ B i ⋙ modulePullback B p).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((modulePullback B f ⋙ moduleJ B k).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (moduleJ B i ⋙ modulePullback B p).mapDerivedCategory
      (modulePullback B f ⋙ moduleJ B k).mapDerivedCategory
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (singleAlpha B k f p i h) (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom

/-- The single-level proper mate of the same clopen projector.
Source: Stacks 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def singleDerivedGamma {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) : r B f ⋙ j B i ⟶ j B k ⋙ r B p :=
  mateEquiv (dAdj B f) (dAdj B p) (singleDerivedAlpha B k f p i h)

/-- The tower derived unit, including the canonical quotient identifications.
Source: Stacks 07A5 (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def towerDerivedUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Towers B X) ℤ) :
    DerivedCategory.Q.obj (((towerDirectImage B f).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (R B f).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (towerDirectImage B f).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K) ≫
    (R B f).map ((DerivedCategory.quotientCompQhIso _).hom.app K)

/-- The existing exact evaluation factorization with the original coefficient universe.
Source: Stacks 015F (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def evaluationFactors (X : Scheme.{u}) (n : ℕ) :=
  @Functor.mapDerivedCategoryFactors (Towers B X) inferInstance
    (clopenTowerAbelian B X) (towers_hasDerivedCategory B X)
    (Modules B X) inferInstance (modulesAbelian B X)
    (inferInstance : HasDerivedCategory (Modules B X))
    ((evaluation ℕᵒᵖ (Modules B X)).obj (op n)) inferInstance inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation uses the canonical K-injective resolution comparison.
Source: Stacks 0D6E and normalized derived tower evaluation
(blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the tower realization and levelwise abelian theorems give unbounded K-injective
resolutions. Evaluation has an exact left adjoint, hence evaluates a K-injective tower
to a K-injective complex. On that representative both direct images are the identical
complex. Apply the unit normalization of lem-weil-pbc-tower-derived-evaluation-normalization;
its counit equation identifies this comparison with the specified mate evalR. -/
theorem evaluation_resolution {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (I : CochainComplex (Towers B X) ℤ) [I.IsKInjective] :
    IsIso (evalR B f n) ∧
    (evaluationFactors B Y n).inv.app
        (((towerDirectImage B f).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (ev B Y n).map (towerDerivedUnit B f I) ≫
      (evalR B f n).app (DerivedCategory.Q.obj I) ≫
      (r B f).map
        ((evaluationFactors B X n).hom.app I) =
      Scheme.proEtaleRingDirectImageDerivedUnit f (coefficients B Y) (coefficients B X)
        (constantRingIso B f)
        (((evaluation ℕᵒᵖ (Modules B X)).obj (op n)).mapHomologicalComplex (.up ℤ) |>.obj I) := by
  refine ⟨evalR_isIso B f n, ?_⟩
  have hh := evaluation_resolution_normalized
    (L := modulePullback B f) (R := moduleDirectImage B f)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)) n I
  rw [← evalG_eq B f n] at hh
  change (evaluationFactors B Y n).inv.app
      (((towerDirectImage B f).mapHomologicalComplex (.up ℤ)).obj I) ≫
    (ev B Y n).map (towerDerivedUnit B f I) ≫
    (evalR B f n).app (DerivedCategory.Q.obj I) ≫
    (r B f).map ((evaluationFactors B X n).hom.app I) =
      Scheme.proEtaleRingDirectImageDerivedUnit f (coefficients B Y) (coefficients B X)
        (constantRingIso B f)
        ((((evaluation ℕᵒᵖ (Modules B X)).obj (op n)).mapHomologicalComplex (.up ℤ)).obj I)
    at hh
  exact hh

/-- Evaluation preserves every transpose for the specified derived adjunctions.
Source: Stacks 07A6, 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the normalized evaluation theorem gives the counit equation. Evaluate a map
and its transpose, substitute that equation, and use naturality. Taking the identity
of inverse image gives the unit equation; taking the counit gives its preservation. -/
theorem evaluation_transpose {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Derived B Y) (N : Derived B X) (t : (G B f).obj M ⟶ N) :
    (ev B Y n).map ((adj B f).homEquiv M N t) ≫ (evalR B f n).app N =
      (dAdj B f).homEquiv _ _
        ((evalG B f n).inv.app M ≫ (ev B X n).map t) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [(ev B Y n).map_comp, Category.assoc]
  rw [show (ev B Y n).map ((R B f).map t) ≫ (evalR B f n).app N =
    (evalR B f n).app ((G B f).obj M) ≫ (r B f).map ((ev B X n).map t) from
      (evalR B f n).naturality t]
  have hu := unit_mateEquiv (adj B f) (dAdj B f)
    (TwoSquare.mk _ _ _ _ (evalG B f n).inv) M
  change (ev B Y n).map ((adj B f).unit.app M) ≫
    (evalR B f n).app ((G B f).obj M) =
      (dAdj B f).unit.app ((ev B Y n).obj M) ≫
        (r B f).map ((evalG B f n).inv.app M) at hu
  rw [← Category.assoc, hu, (r B f).map_comp, Category.assoc]

/-- Both proper-adjunction structure maps are preserved by evaluation.
Source: Stacks 07A6, 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: specialize evaluation_transpose first to the identity on G_f M, giving the
unit equation. Specialize it to the counit on N and use the triangle identity,
giving the counit equation. The same normalized evalG and evalR occur throughout. -/
theorem evaluation_units_counits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (∀ M : Derived B Y,
      (ev B Y n).map ((adj B f).unit.app M) ≫
          (evalR B f n).app ((G B f).obj M) ≫
          (r B f).map ((evalG B f n).hom.app M) =
        (dAdj B f).unit.app ((ev B Y n).obj M)) ∧
    (∀ N : Derived B X,
      (ev B X n).map ((adj B f).counit.app N) =
        (evalG B f n).hom.app ((R B f).obj N) ≫
          (g B f).map ((evalR B f n).app N) ≫
          (dAdj B f).counit.app ((ev B X n).obj N)) := by
  constructor
  · intro M
    have hu := unit_mateEquiv (adj B f) (dAdj B f)
      (TwoSquare.mk _ _ _ _ (evalG B f n).inv) M
    change (ev B Y n).map ((adj B f).unit.app M) ≫
      (evalR B f n).app ((G B f).obj M) =
        (dAdj B f).unit.app ((ev B Y n).obj M) ≫
          (r B f).map ((evalG B f n).inv.app M) at hu
    rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    erw [(r B f).map_id, Category.comp_id]
  · intro N
    have hc := mateEquiv_counit (adj B f) (dAdj B f)
      (TwoSquare.mk _ _ _ _ (evalG B f n).inv) N
    change (g B f).map ((evalR B f n).app N) ≫
      (dAdj B f).counit.app ((ev B X n).obj N) =
        (evalG B f n).inv.app ((R B f).obj N) ≫
          (ev B X n).map ((adj B f).counit.app N) at hc
    rw [hc, Iso.hom_inv_id_app_assoc]

/-- Evaluation also preserves every transpose for the exact open adjunction.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the ordinary open adjunction and its termwise version have the same evaluated
units and counits. Exact descent preserves these identities. The Hom-equivalence
formula therefore gives the displayed equality; identities and counits recover the
two structure-map equations, including for the empty open. -/
theorem evaluation_open_unit (B : Type (u + 1)) [CommRing B]
    {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (n : ℕ)
    (M : Derived B U) :
    (ev B U n).map ((jAdj B f).unit.app M) ≫
        (evalG B f n).hom.app ((J B f).obj M) =
      (dJAdj B f).unit.app ((ev B U n).obj M) ≫
        (g B f).map ((evalJ B f n).inv.app M) := by
  rw [evalG_eq, evalJ_eq]
  have hu := exact_evaluation_unit (moduleJAdj B f) n M
  rw [exactAdj_jAdj, exactAdj_dJAdj] at hu
  simpa only [J] using hu

theorem evaluation_open_transpose {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (n : ℕ) (M : Derived B U) (N : Derived B X)
    (t : (J B f).obj M ⟶ N) :
    (ev B U n).map ((jAdj B f).homEquiv M N t) ≫ (evalG B f n).hom.app N =
      (dJAdj B f).homEquiv _ _
        ((evalJ B f n).inv.app M ≫ (ev B X n).map t)  := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [(ev B U n).map_comp, Category.assoc]
  rw [show (ev B U n).map ((G B f).map t) ≫ (evalG B f n).hom.app N =
    (evalG B f n).hom.app ((J B f).obj M) ≫
      (g B f).map ((ev B X n).map t) from (evalG B f n).hom.naturality t]
  rw [← Category.assoc, evaluation_open_unit B f n M]
  rw [(g B f).map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation preserves the same alpha, including the specified clopen section projector.
Source: Stacks 03DI, 03DJ, 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: evaluation commutes termwise with inverse image and extension by zero.
The inverse cartesian beta is characterized by the pulled-back open unit. The clopen
projector theorem identifies pi with the first-factor section projection and with
unit followed by the inverse of openToR. Evaluation retains this projector and the
unit-preserving compositors. Descend these exact identities and compose the factors. -/
theorem evaluation_alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) (n : ℕ) (M : Derived B S) :
    (ev B W n).map ((alpha B k f p i h).app M) ≫
        (evalJ B k n).hom.app ((G B f).obj M) ≫
        (j B k).map ((evalG B f n).hom.app M) =
      (evalG B p n).hom.app ((J B i).obj M) ≫
        (g B p).map ((evalJ B i n).hom.app M) ≫
        (singleDerivedAlpha B k f p i h).app ((ev B S n).obj M) := by
  have hα := exactSquare_unique (towerJ B i) (towerPullback B p)
    (towerPullback B f) (towerJ B k) (towerAlpha B k f p i h) (alpha B k f p i h)
    (alpha_eq_localized_singleAlpha B k f p i h)
  have he := evalD_square_trans (moduleJ B i) (modulePullback B p)
    (modulePullback B f) (moduleJ B k) (singleAlpha B k f p i h) M n
  rw [hα, evalJ_eq, evalJ_eq, evalG_eq, evalG_eq]
  exact he

/-- Both mates have the displayed unit-square-counit formula, in their own derived categories.
Source: Stacks 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: substitute G_f, R_f, G_p, R_p, J_i and J_k in def-weil-pbc-adjunction-mate.
The component formula is the unit at J_i R_f M, then R_p of alpha at R_f M,
then R_p J_k of the counit at M. Apply the identical formula at a single level. -/
theorem gamma_formula {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) :
    (∀ M : Derived B V, (gamma B k f p i h).app M =
      (adj B p).unit.app ((J B i).obj ((R B f).obj M)) ≫
        (R B p).map ((alpha B k f p i h).app ((R B f).obj M)) ≫
        (R B p).map ((J B k).map ((adj B f).counit.app M))) ∧
    (∀ N : DerivedCategory (Modules B V), (singleDerivedGamma B k f p i h).app N =
      (dAdj B p).unit.app ((j B i).obj ((r B f).obj N)) ≫
        (r B p).map ((singleDerivedAlpha B k f p i h).app ((r B f).obj N)) ≫
        (r B p).map ((j B k).map ((dAdj B f).counit.app N))) := by
  constructor <;> intro M
  · simp [gamma, mateEquiv]
  · simp [singleDerivedGamma, mateEquiv]

/-- Evaluation carries the proper mate to the single-level mate of the same projector.
Source: Stacks 07A7, 0D6E (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: apply evaluation to the three factors in gamma_formula. Replace the evaluated
unit and counit by their single-level versions using evaluation_transpose and the
normalized direct-image comparison. Replace alpha using evaluation_alpha. Functoriality
preserves their ordered composite, giving exactly the single-level mate formula. -/
theorem evaluation_gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper f] [IsProper p]
    (h : k ≫ p = f ≫ i) (n : ℕ) (M : Derived B V) :
    (ev B T n).map ((gamma B k f p i h).app M) ≫
        (evalR B p n).app ((J B k).obj M) ≫
        (r B p).map ((evalJ B k n).hom.app M) =
      (evalJ B i n).hom.app ((R B f).obj M) ≫
        (j B i).map ((evalR B f n).app M) ≫
        (singleDerivedGamma B k f p i h).app ((ev B V n).obj M) := by
  apply exchangeMate_cube (adj B f) (adj B p) (dAdj B f) (dAdj B p)
    (ev B S n) (ev B V n) (ev B T n) (ev B W n)
    (evalG B f n) (evalJ B i n) (evalJ B k n) (evalG B p n)
    (alpha B k f p i h) (singleDerivedAlpha B k f p i h) (fun X ↦ ?_) M
  apply (cancel_epi ((g B p).map ((evalJ B i n).hom.app X))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_mono ((evalJ B k n).hom.app ((G B f).obj X) ≫
    (j B k).map ((evalG B f n).hom.app X))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(j B k).map_id, Category.comp_id]
  apply (cancel_epi ((evalG B p n).hom.app ((J B i).obj X))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simpa only [Category.assoc] using evaluation_alpha B k f p i h n X

variable {B} {Λ : Type (u + 1)} [CommRing Λ]

/-- Apply the existing constant-sheaf functor to the coefficient homomorphism.
Source: Stacks 0H7J (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def coefficientMap (φ : B →+* Λ) (X : Scheme.{u}) : coefficients B X ⟶ coefficients Λ X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)

/-- Constant-section identifications commute with any coefficient homomorphism.
Source: Stacks 0H7J, 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the tower realization theorem's coefficient-naturality clause computes both
adjoints on a constant section b as the constant section φ(b). Sheafification's
universal property gives equality, and taking inverse-image adjoints gives this square. -/
theorem coefficient_square (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantRingIso B f).hom ≫ coefficientMap φ X =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap φ Y) ≫
        (constantRingIso Λ f).hom := by
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f (CommRingCat.ofHom φ)).symm

/-- The recorded sectionwise restriction functor for the actual constant ring-sheaf map.
Source: Stacks 03DA (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev moduleRes (φ : B →+* Λ) (X : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (coefficientMap φ X)

/-- Exactness on kernels, before localization.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance moduleRes_limits (φ : B →+* Λ) (X : Scheme.{u}) :
    PreservesFiniteLimits (moduleRes φ X) :=
  (Scheme.proEtaleRingRestrictScalars_properties (coefficientMap φ X)).1

/-- Exactness on cokernels, before localization.
Source: Stacks 03CY (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
instance moduleRes_colimits (φ : B →+* Λ) (X : Scheme.{u}) :
    PreservesFiniteColimits (moduleRes φ X) :=
  (Scheme.proEtaleRingRestrictScalars_properties (coefficientMap φ X)).2.1

/-- Exact descent of scalar restriction, on ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
abbrev Res (φ : B →+* Λ) (X : Scheme.{u}) :
    DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules B X) :=
  (moduleRes φ X).mapDerivedCategory

/-- The canonical ordinary scalar/inverse-image comparison, with direction as displayed.
Source: Stacks 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarGModule (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback Λ f ⋙ moduleRes φ X ≅ moduleRes φ Y ⋙ modulePullback B f :=
  (@asIso _ _ _ _
    (Scheme.proEtaleRingRestrictionPullbackInv f (coefficients B Y) (coefficients Λ Y)
      (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
      (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f))
    (Scheme.proEtaleRingRestrictionPullbackInv_isIso f (coefficients B Y) (coefficients Λ Y)
      (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
      (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f))).symm

/-- The canonical inverse-image scalar comparison after exact descent.
Source: Stacks 0D6D (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarG (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    g Λ f ⋙ Res φ X ≅ Res φ Y ⋙ g B f :=
  Scheme.proEtaleRingRestrictionDerivedPullback f (coefficients B Y) (coefficients Λ Y)
    (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
    (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f)

/-- The canonical resolution-normalized derived direct-image scalar comparison.
Source: Stacks 0D6E (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarR (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    r Λ f ⋙ Res φ Y ≅ Res φ X ⋙ r B f :=
  Scheme.proEtaleRingRestrictionDerivedDirectImage f (coefficients B Y) (coefficients Λ Y)
    (coefficients B X) (coefficients Λ X) (coefficientMap φ Y) (coefficientMap φ X)
    (constantRingIso B f) (constantRingIso Λ f) (coefficient_square φ f)

/-- The ordinary open comparison in the inverse direction, fixed by its open-unit transpose.
Source: Stacks 03DI (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarJInv (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    moduleRes φ U ⋙ moduleJ B f ⟶ moduleJ Λ f ⋙ moduleRes φ X :=
  ((mateEquiv (moduleJAdj Λ f) (moduleJAdj B f)).symm (scalarGModule φ f).hom).natTrans

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The open-unit transpose is invertible for arbitrary coefficient maps.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: identify the pro-etale open site with the slice. Apply
lem-cbc-ringed-open-scalar-adjunction: on the extension presheaf every direct-sum
summand is unchanged, its map is identity, and the remaining values are zero.
The theorem preserves the open units and counits, so uniqueness of transpose
identifies its inverse with scalarJInv. No flatness is needed. -/
theorem scalarJInv_app_isIso (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (M : Modules Λ U) :
    IsIso ((scalarJInv φ f).app M) := by
  have hIso : IsIso (FiniteOpenScalars.openResMap φ f) := by
    -- Paste through fixed coefficient coordinates, then take open inverse mates.
    let α := TwoSquare.mk _ _ _ _ (FiniteOpenScalars.pullRes φ f).hom
    let β := FiniteOpenScalars.fixedPull (A := B) f
    let γ := FiniteOpenScalars.fixedPull (A := Λ) f
    let δ := TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom
    have : IsIso α.natTrans := by dsimp only [α, TwoSquare.mk]; infer_instance
    have : IsIso β.natTrans := FiniteOpenScalars.fixedPull_isIso f
    have : IsIso γ.natTrans := FiniteOpenScalars.fixedPull_isIso f
    have : IsIso δ.natTrans := by dsimp only [δ, TwoSquare.mk]; infer_instance
    have : IsIso (TwoSquare.hComp γ δ).natTrans := by
      dsimp only [TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let oa := moduleJAdj Λ f
    let ob := moduleJAdj B f
    let oc := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) f
    let od := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) f
    have := fixedRestriction_equivalence B U
    have := fixedRestriction_equivalence B X
    have := fixedRestriction_equivalence Λ U
    have := fixedRestriction_equivalence Λ X
    have : IsIso ((mateEquiv oa od).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv γ.natTrans))).natTrans :=
      inverseMate_isIso_of_equivalences oa od _
    have : IsIso ((mateEquiv od oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv δ.natTrans))).natTrans := by
      simp only [δ, TwoSquare.mk, TwoSquare.natTrans, IsIso.Iso.inv_hom]
      rw [← scalarPullbackModel_eq B f Λ φ]
      exact scalarOpenModel_isIso B f Λ φ
    have hw : IsIso ((mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _
          (CategoryTheory.inv (TwoSquare.hComp γ δ).natTrans))).natTrans := by
      rw [inv_hComp, inverseMate_vComp oa od oc]
      dsimp only [TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let w := TwoSquare.mk _ _ _ _ (CategoryTheory.inv (TwoSquare.hComp γ δ).natTrans)
    let t := TwoSquare.hComp α β
    have : IsIso t.natTrans := by
      dsimp only [t, TwoSquare.hComp, TwoSquare.mk]
      infer_instance
    let z := Functor.isoWhiskerRight (FiniteOpenScalars.resFixed φ X) _ ≪≫
      asIso (TwoSquare.hComp γ δ).natTrans ≪≫
      Functor.isoWhiskerLeft (modulePullback Λ f) (FiniteOpenScalars.resFixed φ U).symm
    have ht : CategoryTheory.inv t.natTrans =
        ((w.whiskerRight (FiniteOpenScalars.resFixed φ U).hom).whiskerLeft
          (FiniteOpenScalars.resFixed φ X).inv).natTrans := by
      have hz : t.natTrans = z.hom :=
        congrArg TwoSquare.natTrans (FiniteOpenScalars.resPull_fixed φ f)
      calc
        CategoryTheory.inv t.natTrans = CategoryTheory.inv z.hom :=
          IsIso.inv_eq_inv.mpr hz
        _ = _ := by
          simp only [IsIso.Iso.inv_hom, z, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
            Functor.isoWhiskerRight_inv, Iso.symm_inv, asIso_inv, w,
            TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk, Category.assoc]
    have hi : IsIso ((mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t.natTrans))).natTrans := by
      rw [ht]
      exact inverseMate_iso_edges oa oc (FiniteOpenScalars.resFixed φ U)
        (FiniteOpenScalars.resFixed φ X).symm w
    let x := (mateEquiv oa ob).symm (TwoSquare.mk _ _ _ _ (FiniteOpenScalars.pullRes φ f).inv)
    let y := (mateEquiv ob oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv β.natTrans))
    have : IsIso y.natTrans := inverseMate_isIso_of_equivalences ob oc _
    have he : (mateEquiv oa oc).symm
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t.natTrans)) = TwoSquare.hComp x y := by
      dsimp only [t]
      rw [inv_hComp]
      exact inverseMate_vComp oa ob oc _ _
    rw [he] at hi
    exact isIso_of_hComp x y
  change IsIso ((FiniteOpenScalars.openResMap φ f).app M)
  have := hIso
  infer_instance

set_option linter.style.haveILetI false in
theorem scalarJInv_isIso (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] : IsIso (scalarJInv φ f) := by
  letI : ∀ M : Modules Λ U, IsIso ((scalarJInv φ f).app M) :=
    fun M ↦ scalarJInv_app_isIso φ f M
  exact NatIso.isIso_of_isIso_app _

/-- The canonical section-normalized ordinary open scalar comparison.
Source: Stacks 03DI (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarJModule (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    moduleJ Λ f ⋙ moduleRes φ X ≅ moduleRes φ U ⋙ moduleJ B f :=
  (@asIso _ _ _ _ (scalarJInv φ f) (scalarJInv_isIso φ f)).symm

/-- Exact descent of the same identity on extension presheaves.
Source: Stacks 03DI, 03DJ, 015F (blueprint: lem-cbc-tower-mate-evaluation-scalars). -/
def scalarJ (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    j Λ f ⋙ Res φ X ≅ Res φ U ⋙ j B f :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (scalarJModule φ f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

set_option backward.isDefEq.respectTransparency false in
/-- The scalar comparisons preserve the specified ordinary open unit and counit.
These equations normalize the identity on extension-presheaf generators.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the slice scalar theorem identifies each generator with the same section in
the same summand, and sends the open unit and counit to themselves. Transport
through weakly-etale localization and uniqueness of the unit-preserving adjoint.
These are exactly the two equations of RingedOpenScalar.Equations. -/
theorem scalar_open_normalized (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] :
    ((∀ N : Modules Λ U,
      (moduleRes φ U).map ((moduleJAdj Λ f).unit.app N) ≫
        (scalarGModule φ f).hom.app ((moduleJ Λ f).obj N) ≫
        (modulePullback B f).map ((scalarJModule φ f).hom.app N) =
      (moduleJAdj B f).unit.app ((moduleRes φ U).obj N)) ∧
    (∀ Q : Modules Λ X,
      (scalarJModule φ f).hom.app ((modulePullback Λ f).obj Q) ≫
        (moduleJ B f).map ((scalarGModule φ f).hom.app Q) ≫
        (moduleJAdj B f).counit.app ((moduleRes φ X).obj Q) =
      (moduleRes φ X).map ((moduleJAdj Λ f).counit.app Q))) ∧
    ((∀ N : DerivedCategory (Modules Λ U),
      (Res φ U).map ((dJAdj Λ f).unit.app N) ≫
        (scalarG φ f).hom.app ((j Λ f).obj N) ≫
        (g B f).map ((scalarJ φ f).hom.app N) =
      (dJAdj B f).unit.app ((Res φ U).obj N)) ∧
    (∀ Q : DerivedCategory (Modules Λ X),
      (scalarJ φ f).hom.app ((g Λ f).obj Q) ≫
        (j B f).map ((scalarG φ f).hom.app Q) ≫
        (dJAdj B f).counit.app ((Res φ X).obj Q) =
      (Res φ X).map ((dJAdj Λ f).counit.app Q))) := by
  have hm : ((mateEquiv (moduleJAdj Λ f) (moduleJAdj B f)).symm
      (TwoSquare.mk _ _ _ _ (scalarGModule φ f).hom)).natTrans =
      (scalarJModule φ f).inv := rfl
  have he := SheafOfModules.RingedOpenScalar.equations_of_inverseMate
    (scalarJModule φ f) (scalarGModule φ f).symm
    (moduleJAdj Λ f) (moduleJAdj B f) hm
  refine ⟨he, ?_⟩
  have hu (K : DerivedCategory (Modules Λ U)) := exact_mate
    (moduleJAdj Λ f) (moduleJAdj B f) (scalarGModule φ f) (scalarJModule φ f).symm
    (dJAdj Λ f) (dJAdj B f)
    (by intro L; simpa only [exactAdj, dJAdj] using exactAdj_unit (moduleJAdj Λ f) L)
    (by intro L; simpa only [exactAdj, dJAdj] using exactAdj_unit (moduleJAdj B f) L)
    (by
      intro L
      have hh := unit_mateEquiv_symm (moduleJAdj Λ f) (moduleJAdj B f)
        (TwoSquare.mk _ _ _ _ (scalarGModule φ f).hom) L
      change _ = _ ≫ (modulePullback B f).map
        (((mateEquiv (moduleJAdj Λ f) (moduleJAdj B f)).symm
          (TwoSquare.mk _ _ _ _ (scalarGModule φ f).hom)).natTrans.app L) at hh
      rw [hm] at hh
      exact hh.symm) K
  apply SheafOfModules.RingedOpenScalar.equations_of_inverseMate
    (scalarJ φ f) (scalarG φ f).symm (dJAdj Λ f) (dJAdj B f)
  ext K
  apply ((dJAdj B f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu' : (dJAdj B f).unit.app ((Res φ U).obj K) ≫
      (g B f).map ((scalarJ φ f).inv.app K) =
    (Res φ U).map ((dJAdj Λ f).unit.app K) ≫
      (scalarG φ f).hom.app ((j Λ f).obj K) := by
    have hG : scalarG φ f =
        Functor.mapDerivedCategorySquareIso (scalarGModule φ f) := by rfl
    rw [hG]
    simpa only [scalarJ, Functor.mapDerivedCategorySquareIso, Iso.trans_inv,
      Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc] using hu K
  exact (unit_mateEquiv_symm (dJAdj Λ f) (dJAdj B f)
    (TwoSquare.mk _ _ _ _ (scalarG φ f).hom) K).symm.trans hu'.symm

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction retains the specified identity/zero clopen section projector.
Source: Stacks 03DI, 09AE (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the clopen projector theorem identifies pi with projection from the two
section factors. Restriction retains both factors and their map (x,y) to x.
The open scalar comparison is identity on extension presheaves. Its unit and
counit normalization identifies the adjunction-defined pi with that same projection,
so the equality holds for the specified maps, before localization. -/
theorem scalar_projector (φ : B →+* Λ) {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] [IsClosedImmersion f] (M : Modules Λ X) :
    (moduleRes φ X).map ((clopenModulePi Λ f).app M) ≫
        (scalarJModule φ f).hom.app ((modulePullback Λ f).obj M) ≫
        (moduleJ B f).map ((scalarGModule φ f).hom.app M) =
      (clopenModulePi B f).app ((moduleRes φ X).obj M) := by
  let O : X.Opens :=
    ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hpΛ := (clopenModule_section_projector Λ f O.ι (Scheme.Opens.range_ι O)).2.1 M
  have hpB := (clopenModule_section_projector B f O.ι
    (Scheme.Opens.range_ι O)).2.1 ((moduleRes φ X).obj M)
  have hu := (scalar_open_normalized φ f).1.1 ((modulePullback Λ f).obj M)
  have hn := (scalarGModule φ f).hom.naturality ((clopenModulePi Λ f).app M)
  dsimp only [Functor.comp_map] at hn
  have he : (modulePullback B f).map
      ((moduleRes φ X).map ((clopenModulePi Λ f).app M) ≫
        (scalarJModule φ f).hom.app ((modulePullback Λ f).obj M) ≫
        (moduleJ B f).map ((scalarGModule φ f).hom.app M)) =
      (modulePullback B f).map ((clopenModulePi B f).app
        ((moduleRes φ X).obj M)) := by
    apply (cancel_epi ((scalarGModule φ f).hom.app M)).1
    simp only [Functor.map_comp, ← Category.assoc]
    erw [← hn, hpΛ]
    simp only [Category.assoc]
    erw [reassoc_of% hu]
    erw [← (moduleJAdj B f).unit.naturality ((scalarGModule φ f).hom.app M), hpB]
    rfl
  have ht := clopenModuleToDirect_isIso B f
  apply (cancel_mono ((clopenModuleToDirect B f).app
    ((modulePullback B f).obj ((moduleRes φ X).obj M)))).1
  apply ((clopenModuleAdj B f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ z ≫ (modulePullback B f).map
      ((clopenModuleToDirect B f).app
        ((modulePullback B f).obj ((moduleRes φ X).obj M))) ≫
      (clopenModuleAdj B f).counit.app
        ((modulePullback B f).obj ((moduleRes φ X).obj M))) he

section ScalarCalculations

attribute [local irreducible] Functor.leftAdjoint Scheme.proEtaleRingModulePullback

attribute [local irreducible] constantSheaf presheafToSheaf SheafOfModules.restrictScalars

private theorem moduleRes_eq (φ : B →+* Λ) (X : Scheme.{u}) :
    moduleRes φ X = FiniteOpenScalars.res φ X := rfl

private theorem scalarGModule_eq (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarGModule φ f = (FiniteOpenScalars.pullRes φ f).symm := rfl

attribute [local irreducible] scalarGModule

section ScalarCompatibility

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  {u₀ : A₀ ⥤ B₀} {u₁ : A₁ ⥤ B₁} {u₂ : A₂ ⥤ B₂}
  {F G H : A₀ ⥤ A₁} {F' G' H' : B₀ ⥤ B₁}

private theorem scalarPaste_naturality {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') {M N : A₀} (f : M ⟶ N) :
    u₂.map (P.map (F.map f)) ≫ (b.hom.app (F.obj N) ≫ P'.map (a.hom.app N)) =
      (b.hom.app (F.obj M) ≫ P'.map (a.hom.app M)) ≫ P'.map (F'.map (u₀.map f)) := by
  have ha := a.hom.naturality f
  have hb := b.hom.naturality (F.map f)
  dsimp only [Functor.comp_map] at ha hb
  rw [← Category.assoc, hb, Category.assoc, ← P'.map_comp, ha, P'.map_comp,
    Category.assoc]

private def scalarPaste {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') :
    (F ⋙ P) ⋙ u₂ ≅ u₀ ⋙ (F' ⋙ P') :=
  NatIso.ofComponents (fun M ↦ b.app (F.obj M) ≪≫ P'.mapIso (a.app M))
    (fun f ↦ scalarPaste_naturality a b f)

private theorem scalarPaste_hom {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') (M : A₀) :
    (scalarPaste a b).hom.app M = b.hom.app (F.obj M) ≫ P'.map (a.hom.app M) := rfl

private theorem scalarPaste_inv {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P') (M : A₀) :
    (scalarPaste a b).inv.app M = P'.map (a.inv.app M) ≫ b.inv.app (F.obj M) := rfl

private def ScalarCompatible (t : F ⟶ G) (t' : F' ⟶ G')
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : G ⋙ u₁ ≅ u₀ ⋙ G') : Prop :=
  ∀ M, u₁.map (t.app M) ≫ b.hom.app M = a.hom.app M ≫ t'.app (u₀.obj M)

private theorem scalarCompatible_apply
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'}
    {t : F ⟶ G} {t' : F' ⟶ G'} (h : ScalarCompatible t t' a b) (M : A₀) :
    u₁.map (t.app M) ≫ b.hom.app M = a.hom.app M ≫ t'.app (u₀.obj M) := h M

private theorem scalarCompatible_of_inverse
    (t : F ⟶ G) (t' : F' ⟶ G')
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : G ⋙ u₁ ≅ u₀ ⋙ G')
    (h : ∀ M, a.inv.app M ≫ u₁.map (t.app M) = t'.app (u₀.obj M) ≫ b.inv.app M) :
    ScalarCompatible t t' a b := by
  intro M
  apply (cancel_epi (a.inv.app M)).1
  apply (cancel_mono (b.inv.app M)).1
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Iso.inv_hom_id_app_assoc, Functor.comp_obj] using h M

private theorem scalarCompatible_identity (a : F ⋙ u₁ ≅ u₀ ⋙ F') :
    ScalarCompatible (𝟙 F) (𝟙 F') a a := by
  intro M
  dsimp only [Functor.comp_obj]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

private theorem scalarCompatible_of_id (a : F ⋙ u₁ ≅ u₀ ⋙ F')
    (t : F ⟶ F) (t' : F' ⟶ F') (ht : t = 𝟙 F) (ht' : t' = 𝟙 F') :
    ScalarCompatible t t' a a := by
  subst t
  subst t'
  exact scalarCompatible_identity a

private theorem scalarCompatible_transport {I : Type*}
    (L : I → (A₀ ⥤ A₁)) (L' : I → (B₀ ⥤ B₁))
    (a : ∀ x, L x ⋙ u₁ ≅ u₀ ⋙ L' x)
    (t : ∀ {x y : I}, x = y → (L x ⟶ L y))
    (t' : ∀ {x y : I}, x = y → (L' x ⟶ L' y))
    (ht : ∀ x, t (rfl : x = x) = 𝟙 (L x))
    (ht' : ∀ x, t' (rfl : x = x) = 𝟙 (L' x))
    {x y : I} (h : x = y) : ScalarCompatible (t h) (t' h) (a x) (a y) := by
  subst y
  exact scalarCompatible_of_id (a x) _ _ (ht x) (ht' x)

private theorem scalarCompatible_comp
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {c : H ⋙ u₁ ≅ u₀ ⋙ H'}
    {t : F ⟶ G} {t' : F' ⟶ G'} {s : G ⟶ H} {s' : G' ⟶ H'}
    (ht : ScalarCompatible t t' a b) (hs : ScalarCompatible s s' b c) :
    ScalarCompatible (t ≫ s) (t' ≫ s') a c := by
  intro M
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [hs M, reassoc_of% (ht M)]

private theorem scalarCompatible_inv
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {e : F ≅ G} {e' : F' ≅ G'}
    (h : ScalarCompatible e.hom e'.hom a b) :
    ScalarCompatible e.inv e'.inv b a := by
  intro M
  apply (cancel_epi (u₁.map (e.hom.app M))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% (h M), Iso.hom_inv_id_app, Category.comp_id]

private theorem scalarCompatible_whiskerLeft
    {P : A₂ ⥤ A₀} {P' : B₂ ⥤ B₀} (c : P ⋙ u₀ ≅ u₂ ⋙ P')
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {t : F ⟶ G} {t' : F' ⟶ G'}
    (h : ScalarCompatible t t' a b) :
    ScalarCompatible (Functor.whiskerLeft P t) (Functor.whiskerLeft P' t')
      (scalarPaste c a) (scalarPaste c b) := by
  intro M
  simp only [Functor.whiskerLeft_app, scalarPaste_hom, Category.assoc]
  rw [reassoc_of% (h (P.obj M))]
  exact congrArg (a.hom.app (P.obj M) ≫ ·) (t'.naturality (c.hom.app M)).symm

private theorem scalarCompatible_whiskerRight
    {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂} (c : P ⋙ u₂ ≅ u₁ ⋙ P')
    {a : F ⋙ u₁ ≅ u₀ ⋙ F'} {b : G ⋙ u₁ ≅ u₀ ⋙ G'} {t : F ⟶ G} {t' : F' ⟶ G'}
    (h : ScalarCompatible t t' a b) :
    ScalarCompatible (Functor.whiskerRight t P) (Functor.whiskerRight t' P')
      (scalarPaste a c) (scalarPaste b c) := by
  intro M
  have hn := c.hom.naturality (t.app M)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.whiskerRight_app, scalarPaste_hom, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, h M, Functor.map_comp]

private theorem scalarPaste_refl_right (a : F ⋙ u₁ ≅ u₀ ⋙ F') :
    scalarPaste (P := 𝟭 A₁) (P' := 𝟭 B₁) a (Iso.refl u₁) = a := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [scalarPaste_hom, Iso.refl_hom, NatTrans.id_app,
    Functor.id_map]
  erw [Category.id_comp]

private theorem scalarCompatible_projector
    {P : A₁ ⥤ A₀} {P' : B₁ ⥤ B₀}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₀ ≅ u₁ ⋙ P')
    (t : 𝟭 A₀ ⟶ F ⋙ P) (t' : 𝟭 B₀ ⟶ F' ⋙ P')
    (h : ∀ M, u₀.map (t.app M) ≫ b.hom.app (F.obj M) ≫ P'.map (a.hom.app M) =
      t'.app (u₀.obj M)) :
    ScalarCompatible (u₀ := u₀) (u₁ := u₀) (F := 𝟭 A₀) (F' := 𝟭 B₀)
      t t' (Iso.refl u₀) (scalarPaste a b) := by
  intro M
  simp only [scalarPaste_hom, Iso.refl_hom, NatTrans.id_app]
  exact (h M).trans (Category.id_comp _).symm

private theorem scalarCompatible_associator
    {A₃ B₃ : Type*} [Category A₃] [Category B₃]
    {u₃ : A₃ ⥤ B₃} {P : A₁ ⥤ A₂} {P' : B₁ ⥤ B₂}
    {Q : A₂ ⥤ A₃} {Q' : B₂ ⥤ B₃}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₂ ≅ u₁ ⋙ P')
    (c : Q ⋙ u₃ ≅ u₂ ⋙ Q') :
    ScalarCompatible (Functor.associator F P Q).hom
      (Functor.associator F' P' Q').hom
      (scalarPaste (scalarPaste a b) c) (scalarPaste a (scalarPaste b c)) := by
  intro M
  simp only [Functor.associator_hom_app, CategoryTheory.Functor.map_id,
    scalarPaste_hom, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]

private def scalarAlphaPaste
    {A₃ A₄ : Type*} [Category A₃] [Category A₄]
    (Q : A₀ ⥤ A₁) (S : A₁ ⥤ A₂) (J : A₂ ⥤ A₁) (K : A₁ ⥤ A₃)
    (I : A₀ ⥤ A₄) (P : A₄ ⥤ A₃) (L : A₀ ⥤ A₂) (E : A₂ ⥤ A₃)
    (π : 𝟭 A₁ ⟶ S ⋙ J) (β : I ⋙ P ⟶ Q ⋙ K)
    (jc : J ⋙ K ⟶ E) (gc : Q ⋙ S ⟶ L) : I ⋙ P ⟶ L ⋙ E :=
  β ≫ Functor.whiskerRight (Functor.whiskerLeft Q π) K ≫
    Functor.whiskerRight (Functor.associator Q S J).inv K ≫
    (Functor.associator (Q ⋙ S) J K).hom ≫
    Functor.whiskerLeft (Q ⋙ S) jc ≫ Functor.whiskerRight gc E

private theorem scalarCompatible_six
    {A₃ A₄ B₃ B₄ : Type*} [Category A₃] [Category A₄] [Category B₃] [Category B₄]
    {u₃ : A₃ ⥤ B₃} {u₄ : A₄ ⥤ B₄}
    (Q : A₀ ⥤ A₁) (Q' : B₀ ⥤ B₁) (S : A₁ ⥤ A₂) (S' : B₁ ⥤ B₂)
    (J : A₂ ⥤ A₁) (J' : B₂ ⥤ B₁) (K : A₁ ⥤ A₃) (K' : B₁ ⥤ B₃)
    (I : A₀ ⥤ A₄) (I' : B₀ ⥤ B₄) (P : A₄ ⥤ A₃) (P' : B₄ ⥤ B₃)
    (L : A₀ ⥤ A₂) (L' : B₀ ⥤ B₂) (E : A₂ ⥤ A₃) (E' : B₂ ⥤ B₃)
    (aQ : Q ⋙ u₁ ≅ u₀ ⋙ Q') (aS : S ⋙ u₂ ≅ u₁ ⋙ S')
    (aJ : J ⋙ u₁ ≅ u₂ ⋙ J') (aK : K ⋙ u₃ ≅ u₁ ⋙ K')
    (aI : I ⋙ u₄ ≅ u₀ ⋙ I') (aP : P ⋙ u₃ ≅ u₄ ⋙ P')
    (aL : L ⋙ u₂ ≅ u₀ ⋙ L') (aE : E ⋙ u₃ ≅ u₂ ⋙ E')
    (π : 𝟭 A₁ ⟶ S ⋙ J) (π' : 𝟭 B₁ ⟶ S' ⋙ J')
    (β : I ⋙ P ⟶ Q ⋙ K) (β' : I' ⋙ P' ⟶ Q' ⋙ K')
    (jc : J ⋙ K ⟶ E) (jc' : J' ⋙ K' ⟶ E')
    (gc : Q ⋙ S ⟶ L) (gc' : Q' ⋙ S' ⟶ L')
    (hπ : ∀ M, u₁.map (π.app M) ≫ aJ.hom.app (S.obj M) ≫ J'.map (aS.hom.app M) =
      π'.app (u₁.obj M))
    (hβ : ScalarCompatible β β' (scalarPaste aI aP) (scalarPaste aQ aK))
    (hj : ScalarCompatible jc jc' (scalarPaste aJ aK) aE)
    (hg : ScalarCompatible gc gc' (scalarPaste aQ aS) aL) :
    ScalarCompatible (scalarAlphaPaste Q S J K I P L E π β jc gc)
      (scalarAlphaPaste Q' S' J' K' I' P' L' E' π' β' jc' gc')
      (scalarPaste aI aP) (scalarPaste aL aE) := by
  unfold scalarAlphaPaste
  have hpi := scalarCompatible_projector aS aJ π π' hπ
  have hpiq := scalarCompatible_whiskerLeft aQ hpi
  rw [scalarPaste_refl_right] at hpiq
  have hpiqb := scalarCompatible_whiskerRight aK hpiq
  have hassoc₁ := scalarCompatible_whiskerRight aK
    (scalarCompatible_inv (e := Functor.associator Q S J)
      (e' := Functor.associator Q' S' J') (scalarCompatible_associator aQ aS aJ))
  have hassoc₂ := scalarCompatible_associator (scalarPaste aQ aS) aJ aK
  have hgj := scalarCompatible_whiskerLeft (scalarPaste aQ aS) hj
  have hgk := scalarCompatible_whiskerRight aE hg
  exact scalarCompatible_comp hβ (scalarCompatible_comp hpiqb
    (scalarCompatible_comp hassoc₁ (scalarCompatible_comp hassoc₂
      (scalarCompatible_comp hgj hgk))))

private theorem scalarCompatible_paste_app
    {A₃ B₃ : Type*} [Category A₃] [Category B₃] {u₃ : A₃ ⥤ B₃}
    {L : A₀ ⥤ A₂} {L' : B₀ ⥤ B₂} {P : A₁ ⥤ A₃} {P' : B₁ ⥤ B₃}
    {K : A₂ ⥤ A₃} {K' : B₂ ⥤ B₃}
    (a : F ⋙ u₁ ≅ u₀ ⋙ F') (b : P ⋙ u₃ ≅ u₁ ⋙ P')
    (c : L ⋙ u₂ ≅ u₀ ⋙ L') (d : K ⋙ u₃ ≅ u₂ ⋙ K')
    (t : F ⋙ P ⟶ L ⋙ K) (t' : F' ⋙ P' ⟶ L' ⋙ K')
    (ht : ScalarCompatible t t' (scalarPaste a b) (scalarPaste c d)) (M : A₀) :
    u₃.map (t.app M) ≫ d.hom.app (L.obj M) ≫ K'.map (c.hom.app M) =
      b.hom.app (F.obj M) ≫ P'.map (a.hom.app M) ≫ t'.app (u₀.obj M) := by
  simpa only [scalarPaste_hom, Category.assoc] using ht M

private theorem scalarCompatible_beta
    {A₃ B₃ : Type*} [Category A₃] [Category B₃] {u₃ : A₃ ⥤ B₃}
    (J : A₀ ⥤ A₁) (S : A₁ ⥤ A₀) (Jp : A₂ ⥤ A₃) (Sp : A₃ ⥤ A₂)
    (P : A₀ ⥤ A₂) (Q : A₁ ⥤ A₃)
    (J' : B₀ ⥤ B₁) (S' : B₁ ⥤ B₀) (Jp' : B₂ ⥤ B₃) (Sp' : B₃ ⥤ B₂)
    (P' : B₀ ⥤ B₂) (Q' : B₁ ⥤ B₃)
    (ad : J ⊣ S) (ad' : J' ⊣ S') (ap : Jp ⊣ Sp) (ap' : Jp' ⊣ Sp')
    (rJ : J ⋙ u₁ ≅ u₀ ⋙ J') (rS : S ⋙ u₀ ≅ u₁ ⋙ S')
    (rJp : Jp ⋙ u₃ ≅ u₂ ⋙ Jp') (rSp : Sp ⋙ u₂ ≅ u₃ ⋙ Sp')
    (rP : P ⋙ u₂ ≅ u₀ ⋙ P') (rQ : Q ⋙ u₃ ≅ u₁ ⋙ Q')
    (β : J ⋙ Q ≅ P ⋙ Jp) (β' : J' ⋙ Q' ≅ P' ⋙ Jp')
    (σ : S ⋙ P ⟶ Q ⋙ Sp) (σ' : S' ⋙ P' ⟶ Q' ⋙ Sp')
    (hu : ∀ M, ad'.unit.app (u₀.obj M) ≫ S'.map (rJ.inv.app M) ≫
      rS.inv.app (J.obj M) = u₀.map (ad.unit.app M))
    (hu' : ∀ M, ap'.unit.app (u₂.obj M) ≫ Sp'.map (rJp.inv.app M) ≫
      rSp.inv.app (Jp.obj M) = u₂.map (ap.unit.app M))
    (hb : ∀ M, ap.unit.app (P.obj M) ≫ Sp.map (β.inv.app M) =
      P.map (ad.unit.app M) ≫ σ.app (J.obj M))
    (hb' : ∀ M, ap'.unit.app (P'.obj M) ≫ Sp'.map (β'.inv.app M) =
      P'.map (ad'.unit.app M) ≫ σ'.app (J'.obj M))
    (hσ : ∀ M, σ'.app (u₁.obj M) ≫ Sp'.map (rQ.inv.app M) ≫
        rSp.inv.app (Q.obj M) =
      P'.map (rS.inv.app M) ≫ rP.inv.app (S.obj M) ≫ u₂.map (σ.app M)) :
    ScalarCompatible β.hom β'.hom (scalarPaste rJ rQ) (scalarPaste rP rJp) := by
  let c := (scalarPaste rJ rQ).symm
  let d := (scalarPaste rP rJp).symm
  have hc (M : A₀) : c.hom.app M ≫
      u₃.map (β.hom.app M) =
    β'.hom.app (u₀.obj M) ≫ d.hom.app M := by
    have hi : d.hom.app M ≫
        u₃.map (β.inv.app M) =
      β'.inv.app (u₀.obj M) ≫ c.hom.app M := by
      apply (ap'.homEquiv _ _).injective
      apply (cancel_mono (rSp.inv.app
        (Q.obj (J.obj M)))).1
      simp only [Adjunction.homEquiv_unit, c, d, Iso.symm_hom, scalarPaste_inv,
        Functor.map_comp, Category.assoc]
      have hnu := ap'.unit.naturality (rP.inv.app M)
      simp only [Functor.id_map, Functor.comp_map] at hnu
      rw [← reassoc_of% hnu]
      have hn := rSp.inv.naturality
        (β.inv.app M)
      simp only [Functor.comp_map, Functor.comp_obj] at hn
      rw [hn, reassoc_of% (hu' (P.obj M))]
      slice_lhs 2 3 => rw [← Functor.map_comp, hb M, Functor.map_comp]
      slice_rhs 1 2 => rw [hb' (u₀.obj M)]
      have hs := σ'.naturality
        (rJ.inv.app M)
      simp only [Functor.comp_map, Functor.comp_obj] at hs
      slice_rhs 2 3 => rw [← hs]
      slice_rhs 3 5 =>
        rw [hσ]
      slice_rhs 1 3 =>
        rw [← Functor.map_comp, ← Functor.map_comp]
        erw [hu]
      have hn' := rP.inv.naturality (ad.unit.app M)
      simp only [Functor.comp_map, Functor.comp_obj] at hn'
      erw [← reassoc_of% hn']
      simp only [Category.assoc]
    apply (cancel_mono (u₃.map
      (β.inv.app M))).1
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hi]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj]
    exact (Category.id_comp _).symm
  apply scalarCompatible_of_inverse
  simpa only [c, d, Iso.symm_hom] using hc

end ScalarCompatibility

attribute [local irreducible] scalarPaste scalarAlphaPaste modulePullback ScalarCompatible

private theorem scalar_pull_comp (φ : B →+* Λ) {U V X : Scheme.{u}}
    (f : U ⟶ V) (g : V ⟶ X) :
    ScalarCompatible (moduleGComp Λ f g).hom (moduleGComp B f g).hom
      (scalarGModule φ (f ≫ g))
      (scalarPaste (scalarGModule φ g) (scalarGModule φ f)) := by
  apply scalarCompatible_of_inverse
  intro M
  have hh := FiniteOpenScalars.pullRes_comp φ f g M
  simpa only [scalarPaste_inv, scalarGModule_eq, Iso.symm_inv,
    moduleRes_eq, Functor.comp_obj, Category.assoc] using hh.symm

private theorem scalar_pull_square (φ : B →+* Λ)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (h : a ≫ j = j' ≫ g) (M : Modules Λ X) :
    (moduleSquareG B a j' j g h).inv.app ((moduleRes φ X).obj M) ≫
        (modulePullback B j').map ((scalarGModule φ g).inv.app M) ≫
        (scalarGModule φ j').inv.app ((modulePullback Λ g).obj M) =
      (modulePullback B a).map ((scalarGModule φ j).inv.app M) ≫
        (scalarGModule φ a).inv.app ((modulePullback Λ j).obj M) ≫
        (moduleRes φ U').map ((moduleSquareG Λ a j' j g h).inv.app M) := by
  simpa only [scalarGModule_eq, Iso.symm_inv, moduleRes_eq, Functor.comp_obj] using
    FiniteOpenScalars.pullRes_square φ a j' j g h M

private theorem scalar_open_unit_inverse (φ : B →+* Λ) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M : Modules Λ U) :
    (moduleJAdj B j).unit.app ((moduleRes φ U).obj M) ≫
        (modulePullback B j).map ((scalarJModule φ j).inv.app M) ≫
        (scalarGModule φ j).inv.app ((moduleJ Λ j).obj M) =
      (moduleRes φ U).map ((moduleJAdj Λ j).unit.app M) := by
  have hh := unit_mateEquiv_symm (moduleJAdj Λ j) (moduleJAdj B j)
    (TwoSquare.mk _ _ _ _ (scalarGModule φ j).hom) M
  change (moduleRes φ U).map ((moduleJAdj Λ j).unit.app M) ≫
      (scalarGModule φ j).hom.app ((moduleJ Λ j).obj M) =
    (moduleJAdj B j).unit.app ((moduleRes φ U).obj M) ≫
      (modulePullback B j).map ((scalarJModule φ j).inv.app M) at hh
  rw [← Category.assoc, ← hh, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]

private theorem scalar_beta_unit (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (sq : IsPullback a j' j g) (M : Modules A U) :
    (moduleJAdj A j').unit.app ((modulePullback A a).obj M) ≫
        (modulePullback A j').map ((openBetaModule A a j' j g h sq).inv.app M) =
      (modulePullback A a).map ((moduleJAdj A j).unit.app M) ≫
        (moduleSquareG A a j' j g h).inv.app ((moduleJ A j).obj M) :=
  (openBetaModule_normalized A a j' j g h sq).2 M

private theorem scalar_beta (φ : B →+* Λ)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (sq : IsPullback a j' j g) :
    ScalarCompatible (openBetaModule Λ a j' j g h sq).hom
      (openBetaModule B a j' j g h sq).hom
      (scalarPaste (scalarJModule φ j) (scalarGModule φ g))
      (scalarPaste (scalarGModule φ a) (scalarJModule φ j')) := by
  exact scalarCompatible_beta
    (u₀ := moduleRes φ U) (u₁ := moduleRes φ X)
    (u₂ := moduleRes φ U') (u₃ := moduleRes φ X')
    (moduleJ Λ j) (modulePullback Λ j) (moduleJ Λ j') (modulePullback Λ j')
    (modulePullback Λ a) (modulePullback Λ g)
    (moduleJ B j) (modulePullback B j) (moduleJ B j') (modulePullback B j')
    (modulePullback B a) (modulePullback B g)
    (moduleJAdj Λ j) (moduleJAdj B j) (moduleJAdj Λ j') (moduleJAdj B j')
    (scalarJModule φ j) (scalarGModule φ j) (scalarJModule φ j') (scalarGModule φ j')
    (scalarGModule φ a) (scalarGModule φ g)
    (openBetaModule Λ a j' j g h sq) (openBetaModule B a j' j g h sq)
    (moduleSquareG Λ a j' j g h).inv (moduleSquareG B a j' j g h).inv
    (scalar_open_unit_inverse φ j) (scalar_open_unit_inverse φ j')
    (scalar_beta_unit Λ a j' j g h sq)
    (scalar_beta_unit B a j' j g h sq)
    (scalar_pull_square φ a j' j g h)

private theorem scalarJComp_conjugate (A : Type (u + 1)) [CommRing A]
    {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    conjugateEquiv ((moduleJAdj A j).comp (moduleJAdj A k))
        (moduleJAdj A (j ≫ k)) (openBetaModuleJComp A j k).inv =
      (moduleGComp A j k).inv :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

private theorem scalar_open_comp_inv (φ : B →+* Λ) {U V X : Scheme.{u}}
    (j : U ⟶ V) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] :
    ScalarCompatible (openBetaModuleJComp Λ j k).inv (openBetaModuleJComp B j k).inv
      (scalarJModule φ (j ≫ k))
      (scalarPaste (scalarJModule φ j) (scalarJModule φ k)) := by
  let q := (TwoSquare.mk _ _ _ _ (scalarJModule φ j).inv).vComp
    (TwoSquare.mk _ _ _ _ (scalarJModule φ k).inv)
  let r := TwoSquare.mk _ _ _ _ (scalarJModule φ (j ≫ k)).inv
  have hm {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
      mateEquiv (moduleJAdj Λ j) (moduleJAdj B j)
          (TwoSquare.mk _ _ _ _ (scalarJModule φ j).inv) =
        TwoSquare.mk _ _ _ _ (scalarGModule φ j).hom := by
    change (mateEquiv (moduleJAdj Λ j) (moduleJAdj B j))
      ((mateEquiv (moduleJAdj Λ j) (moduleJAdj B j)).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have hc : q.whiskerRight (openBetaModuleJComp B j k).inv =
      r.whiskerLeft (openBetaModuleJComp Λ j k).inv := by
    apply (mateEquiv ((moduleJAdj Λ j).comp (moduleJAdj Λ k))
      (moduleJAdj B (j ≫ k))).injective
    rw [mateEquiv_conjugateEquiv_vcomp
      ((moduleJAdj Λ j).comp (moduleJAdj Λ k))
      ((moduleJAdj B j).comp (moduleJAdj B k)) (moduleJAdj B (j ≫ k)),
      conjugateEquiv_mateEquiv_vcomp
      ((moduleJAdj Λ j).comp (moduleJAdj Λ k))
      (moduleJAdj Λ (j ≫ k)) (moduleJAdj B (j ≫ k))]
    dsimp only [q, r]
    rw [mateEquiv_hcomp, hm, hm, hm]
    rw [scalarJComp_conjugate, scalarJComp_conjugate]
    apply TwoSquare.ext
    intro M
    simpa only [ScalarCompatible, scalarPaste_hom, TwoSquare.whiskerBottom,
      TwoSquare.whiskerTop, TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using
      (scalarCompatible_apply (scalarCompatible_inv (scalar_pull_comp φ j k)) M).symm
  apply scalarCompatible_of_inverse
  intro M
  have hh := congrArg (fun z ↦ z.app M) hc
  simp only [q, r, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hh
  simpa only [scalarPaste_inv, Category.assoc] using hh.symm

section ScalarEquality

attribute [local irreducible] scalarJModule singleJCongr

private theorem scalar_open_congr (φ : B →+* Λ) {U X : Scheme.{u}}
    {f g : U ⟶ X} [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    ScalarCompatible (u₀ := moduleRes φ U) (u₁ := moduleRes φ X)
      (F := moduleJ Λ f) (G := moduleJ Λ g) (F' := moduleJ B f) (G' := moduleJ B g)
      (singleJCongr Λ h).hom (singleJCongr B h).hom
      (scalarJModule φ f) (scalarJModule φ g) := by
  exact scalarCompatible_transport
    (u₀ := moduleRes φ U) (u₁ := moduleRes φ X)
    (fun x : {q : U ⟶ X // IsOpenImmersion q} ↦
      letI := x.property; moduleJ Λ x.val)
    (fun x ↦ letI := x.property; moduleJ B x.val)
    (fun x ↦ letI := x.property; scalarJModule φ x.val)
    (fun {x y} e ↦ letI := x.property; letI := y.property
      (singleJCongr Λ (congrArg Subtype.val e)).hom)
    (fun {x y} e ↦ letI := x.property; letI := y.property
      (singleJCongr B (congrArg Subtype.val e)).hom)
    (fun x ↦ letI := x.property; singleJCongr_refl Λ x.val)
    (fun x ↦ letI := x.property; singleJCongr_refl B x.val)
    (x := ⟨f, inferInstance⟩) (y := ⟨g, inferInstance⟩) (Subtype.ext h)

private theorem scalar_pull_congr (φ : B →+* Λ) {U X : Scheme.{u}}
    {f g : U ⟶ X} (h : f = g) :
    ScalarCompatible (u₀ := moduleRes φ X) (u₁ := moduleRes φ U)
      (F := modulePullback Λ f) (G := modulePullback Λ g)
      (F' := modulePullback B f) (G' := modulePullback B g)
      (eqToIso (congrArg (modulePullback Λ) h)).hom
      (eqToIso (congrArg (modulePullback B) h)).hom
      (scalarGModule φ f) (scalarGModule φ g) := by
  exact scalarCompatible_transport
    (u₀ := moduleRes φ X) (u₁ := moduleRes φ U)
    (fun q : U ⟶ X ↦ modulePullback Λ q) (fun q ↦ modulePullback B q)
    (fun q ↦ scalarGModule φ q)
    (fun e ↦ (eqToIso (congrArg (modulePullback Λ) e)).hom)
    (fun e ↦ (eqToIso (congrArg (modulePullback B) e)).hom)
    (fun _ ↦ rfl) (fun _ ↦ rfl) h

end ScalarEquality

end ScalarCalculations

section ScalarAlphaCalculations

attribute [local irreducible] scalarPaste scalarAlphaPaste modulePullback ScalarCompatible
attribute [local irreducible] Functor.leftAdjoint Scheme.proEtaleRingModulePullback
attribute [local irreducible] constantSheaf presheafToSheaf SheafOfModules.restrictScalars
attribute [local irreducible] scalarGModule scalarJModule

private def scalarLiftAlpha (A : Type (u + 1)) [CommRing A]
    {U V W S T : Scheme.{u}} (q : U ⟶ S) (b : U ⟶ W) (s : V ⟶ U)
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i]
    (hpb : q ≫ i = b ≫ p) (sq : IsPullback q b i p) (hb : s ≫ b = k) (hq : s ≫ q = f) :
    moduleJ A i ⋙ modulePullback A p ⟶ modulePullback A f ⋙ moduleJ A k :=
  scalarAlphaPaste (modulePullback A q) (modulePullback A s)
    (moduleJ A s) (moduleJ A b) (moduleJ A i) (modulePullback A p)
    (modulePullback A f) (moduleJ A k) (clopenModulePi A s)
    (openBetaModule A q b i p hpb sq).hom
    ((openBetaModuleJComp A s b).hom ≫ (singleJCongr A hb).hom)
    ((moduleGComp A s q).inv ≫ (eqToIso (congrArg (modulePullback A) hq)).hom)

private theorem scalar_lift_alpha (φ : B →+* Λ)
    {U V W S T : Scheme.{u}} (q : U ⟶ S) (b : U ⟶ W) (s : V ⟶ U)
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i]
    (hpb : q ≫ i = b ≫ p) (sq : IsPullback q b i p) (hb : s ≫ b = k) (hq : s ≫ q = f)
    : ScalarCompatible (u₀ := moduleRes φ S) (u₁ := moduleRes φ W)
      (F := moduleJ Λ i ⋙ modulePullback Λ p)
      (G := modulePullback Λ f ⋙ moduleJ Λ k)
      (F' := moduleJ B i ⋙ modulePullback B p)
      (G' := modulePullback B f ⋙ moduleJ B k)
      (scalarLiftAlpha Λ q b s k f p i hpb sq hb hq)
      (scalarLiftAlpha B q b s k f p i hpb sq hb hq)
      (scalarPaste (scalarJModule φ i) (scalarGModule φ p))
      (scalarPaste (scalarGModule φ f) (scalarJModule φ k)) := by
  have hj := scalarCompatible_comp
    (scalarCompatible_inv (e := (openBetaModuleJComp Λ s b).symm)
      (e' := (openBetaModuleJComp B s b).symm) (scalar_open_comp_inv φ s b))
    (scalar_open_congr φ hb)
  have hg := scalarCompatible_comp
    (scalarCompatible_inv (e := moduleGComp Λ s q) (e' := moduleGComp B s q)
      (scalar_pull_comp φ s q))
    (scalar_pull_congr φ hq)
  have ht := scalarCompatible_six
    (u₀ := moduleRes φ S) (u₁ := moduleRes φ U)
    (u₂ := moduleRes φ V) (u₃ := moduleRes φ W) (u₄ := moduleRes φ T)
    (modulePullback Λ q) (modulePullback B q) (modulePullback Λ s) (modulePullback B s)
    (moduleJ Λ s) (moduleJ B s) (moduleJ Λ b) (moduleJ B b)
    (moduleJ Λ i) (moduleJ B i) (modulePullback Λ p) (modulePullback B p)
    (modulePullback Λ f) (modulePullback B f) (moduleJ Λ k) (moduleJ B k)
    (scalarGModule φ q) (scalarGModule φ s) (scalarJModule φ s) (scalarJModule φ b)
    (scalarJModule φ i) (scalarGModule φ p) (scalarGModule φ f) (scalarJModule φ k)
    (clopenModulePi Λ s) (clopenModulePi B s)
    (openBetaModule Λ q b i p hpb sq).hom
    (openBetaModule B q b i p hpb sq).hom
    ((openBetaModuleJComp Λ s b).symm.inv ≫ (singleJCongr Λ hb).hom)
    ((openBetaModuleJComp B s b).symm.inv ≫ (singleJCongr B hb).hom)
    ((moduleGComp Λ s q).inv ≫
      (eqToIso (congrArg (modulePullback Λ) hq)).hom)
    ((moduleGComp B s q).inv ≫
      (eqToIso (congrArg (modulePullback B) hq)).hom)
    (scalar_projector φ s) (scalar_beta φ q b i p hpb sq) hj hg
  exact ht

private theorem scalar_lift_alpha_component (φ : B →+* Λ)
    {U V W S T : Scheme.{u}} (q : U ⟶ S) (b : U ⟶ W) (s : V ⟶ U)
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion b]
    [IsOpenImmersion k] [IsOpenImmersion i]
    (hpb : q ≫ i = b ≫ p) (sq : IsPullback q b i p) (hb : s ≫ b = k) (hq : s ≫ q = f)
    (M : Modules Λ S) :
    (moduleRes φ W).map ((scalarLiftAlpha Λ q b s k f p i hpb sq hb hq).app M) ≫
        (scalarJModule φ k).hom.app ((modulePullback Λ f).obj M) ≫
        (moduleJ B k).map ((scalarGModule φ f).hom.app M) =
      (scalarGModule φ p).hom.app ((moduleJ Λ i).obj M) ≫
        (modulePullback B p).map ((scalarJModule φ i).hom.app M) ≫
        (scalarLiftAlpha B q b s k f p i hpb sq hb hq).app ((moduleRes φ S).obj M) := by
  exact scalarCompatible_paste_app
    (u₀ := moduleRes φ S) (u₁ := moduleRes φ T)
    (u₂ := moduleRes φ V) (u₃ := moduleRes φ W)
    (F := moduleJ Λ i) (F' := moduleJ B i)
    (P := modulePullback Λ p) (P' := modulePullback B p)
    (L := modulePullback Λ f) (L' := modulePullback B f)
    (K := moduleJ Λ k) (K' := moduleJ B k)
    (scalarJModule φ i) (scalarGModule φ p) (scalarGModule φ f) (scalarJModule φ k)
    (scalarLiftAlpha Λ q b s k f p i hpb sq hb hq)
    (scalarLiftAlpha B q b s k f p i hpb sq hb hq)
    (scalar_lift_alpha φ q b s k f p i hpb sq hb hq) M

private theorem scalarLiftAlpha_eq (A : Type (u + 1)) [CommRing A]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper f] [IsProper p] (h : k ≫ p = f ≫ i) :
    scalarLiftAlpha A (pullback.snd p i) (pullback.fst p i)
        (squareLift k f p i h) k f p i (pullback.condition.symm)
        (IsPullback.of_hasPullback p i).flip (pullback.lift_fst k f h)
        (pullback.lift_snd k f h) = singleAlpha A k f p i h := by
  unfold scalarLiftAlpha scalarAlphaPaste singleAlpha
  rfl

/-- Scalar restriction preserves the intrinsic ordinary alpha and its compositors.
Source: Stacks 03DI, 07A7 (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: the inverse cartesian beta transposes the pulled-back open unit. The scalar
open normalization preserves that unit, hence beta and its inverse. Apply
scalar_projector to the clopen lift, then use the constant-section pullback and
unit-preserving open compositors. Composing these identities gives the equation. -/
theorem scalar_alpha (φ : B →+* Λ) {V W S T : Scheme.{u}}
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper f] [IsProper p] (h : k ≫ p = f ≫ i) (M : Modules Λ S) :
    (moduleRes φ W).map ((singleAlpha Λ k f p i h).app M) ≫
        (scalarJModule φ k).hom.app ((modulePullback Λ f).obj M) ≫
        (moduleJ B k).map ((scalarGModule φ f).hom.app M) =
      (scalarGModule φ p).hom.app ((moduleJ Λ i).obj M) ≫
        (modulePullback B p).map ((scalarJModule φ i).hom.app M) ≫
        (singleAlpha B k f p i h).app ((moduleRes φ S).obj M) := by
  have hh := scalar_lift_alpha_component φ (pullback.snd p i) (pullback.fst p i)
    (squareLift k f p i h) k f p i (pullback.condition.symm)
    (IsPullback.of_hasPullback p i).flip (pullback.lift_fst k f h)
    (pullback.lift_snd k f h) M
  rw [scalarLiftAlpha_eq, scalarLiftAlpha_eq] at hh
  exact hh

end ScalarAlphaCalculations

/-- Every derived proper transpose is preserved by the canonical scalar comparisons.
Source: Stacks 07A6, 0D6D, 0D6E (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: specialize lem-weil-pbc-ring-sheaf-change-adjunction to the constant-section
coefficient maps. coefficient_square verifies its compatibility hypothesis.
Its normalized derived direct-image comparison gives exactly this transpose identity,
without requiring scalar restriction to preserve K-injective complexes. -/
theorem scalar_transpose (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Modules Λ Y)) (N : DerivedCategory (Modules Λ X))
    (t : (g Λ f).obj M ⟶ N) :
    (dAdj B f).homEquiv _ _ ((scalarG φ f).inv.app M ≫ (Res φ X).map t) =
      (Res φ Y).map ((dAdj Λ f).homEquiv M N t) ≫ (scalarR φ f).hom.app N := by
  exact (Scheme.proEtaleRingSheafChangeAdjunction f
    (coefficients B Y) (coefficients Λ Y) (coefficients B X) (coefficients Λ X)
    (coefficientMap φ Y) (coefficientMap φ X) (constantRingIso B f)
    (constantRingIso Λ f) (coefficient_square φ f)).2.2 M N t

private theorem scalar_derived_alpha (φ : B →+* Λ) {V W S T : Scheme.{u}}
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper f] [IsProper p] (h : k ≫ p = f ≫ i)
    (M : DerivedCategory (Modules Λ S)) :
    (Res φ W).map ((singleDerivedAlpha Λ k f p i h).app M) ≫
        (scalarJ φ k).hom.app ((g Λ f).obj M) ≫
        (j B k).map ((scalarG φ f).hom.app M) =
      (scalarG φ p).hom.app ((j Λ i).obj M) ≫
        (g B p).map ((scalarJ φ i).hom.app M) ≫
        (singleDerivedAlpha B k f p i h).app ((Res φ S).obj M) := by
  have hs {X Y : Scheme.{u}} (q : X ⟶ Y) :
      scalarG φ q = Functor.mapDerivedCategorySquareIso (scalarGModule φ q) := rfl
  have hj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
      scalarJ φ j = Functor.mapDerivedCategorySquareIso (scalarJModule φ j) := rfl
  rw [hs, hs, hj, hj]
  exact exactSquare_scalar (moduleRes φ S) (moduleRes φ V) (moduleRes φ T)
    (moduleRes φ W) (scalarGModule φ f) (scalarJModule φ i) (scalarJModule φ k)
    (scalarGModule φ p) (singleAlpha Λ k f p i h) (singleAlpha B k f p i h)
    (scalar_alpha φ k f p i h) M

private theorem scalarR_mate (φ : B →+* Λ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : DerivedCategory (Modules Λ X)) :
    (mateEquiv (dAdj Λ f) (dAdj B f)
      (TwoSquare.mk _ _ _ _ (scalarG φ f).inv)).app N = (scalarR φ f).hom.app N := by
  rw [mate_app_eq_adjunct, scalar_transpose]
  dsimp only [Functor.id_obj]
  rw [← (dAdj Λ f).homEquiv_symm_id N, Equiv.apply_symm_apply,
    (Res φ Y).map_id, Category.id_comp]

/-- Scalar restriction identifies the two single-level proper mates on every derived object.
Source: Stacks 07A7, 0D6D, 0D6E (blueprint: lem-cbc-tower-mate-evaluation-scalars).
Proof: descend scalar_alpha exactly. Write t as alpha at R_f N followed by J_k
of the proper counit. scalar_transpose for f and then for p, together with the
normalized open comparisons, identifies its restricted transpose with the B-transpose.
The unit-square-counit formula identifies these with the two singleDerivedGamma maps.
No cancellation by restriction, flatness, cohomological bound or preservation of
K-injectives by scalar restriction enters the argument. -/
theorem scalar_gamma (φ : B →+* Λ) {V W S T : Scheme.{u}}
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper f] [IsProper p] (h : k ≫ p = f ≫ i)
    (N : DerivedCategory (Modules Λ V)) :
    (Res φ T).map ((singleDerivedGamma Λ k f p i h).app N) ≫
        (scalarR φ p).hom.app ((j Λ k).obj N) ≫
        (r B p).map ((scalarJ φ k).hom.app N) =
      (scalarJ φ i).hom.app ((r Λ f).obj N) ≫
        (j B i).map ((scalarR φ f).hom.app N) ≫
        (singleDerivedGamma B k f p i h).app ((Res φ V).obj N) := by
  have hc (M : DerivedCategory (Modules Λ S)) :
      (g B p).map ((scalarJ φ i).inv.app M) ≫
          (scalarG φ p).inv.app ((j Λ i).obj M) ≫
          (Res φ W).map ((singleDerivedAlpha Λ k f p i h).app M) =
        (singleDerivedAlpha B k f p i h).app ((Res φ S).obj M) ≫
          (j B k).map ((scalarG φ f).inv.app M) ≫
          (scalarJ φ k).inv.app ((g Λ f).obj M) := by
    apply (cancel_epi ((g B p).map ((scalarJ φ i).hom.app M))).1
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    apply (cancel_mono ((scalarJ φ k).hom.app ((g Λ f).obj M) ≫
      (j B k).map ((scalarG φ f).hom.app M))).1
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [(j B k).map_id, Category.comp_id]
    apply (cancel_epi ((scalarG φ p).hom.app ((j Λ i).obj M))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    simpa only [Category.assoc] using scalar_derived_alpha φ k f p i h M
  have hh := exchangeMate_cube (dAdj Λ f) (dAdj Λ p) (dAdj B f) (dAdj B p)
    (Res φ S) (Res φ V) (Res φ T) (Res φ W)
    (scalarG φ f) (scalarJ φ i) (scalarJ φ k) (scalarG φ p)
    (singleDerivedAlpha Λ k f p i h) (singleDerivedAlpha B k f p i h) hc N
  rw [scalarR_mate, scalarR_mate] at hh
  exact hh

end AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars
