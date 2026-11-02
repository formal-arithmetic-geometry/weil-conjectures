/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingAffineLineStep
public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineTensorActions.OrdinaryAffineTensorActions
import WeilConjectures.SixFunctors.Etale.Derived.WeilDual

/-! # Tensor strength of the last-coordinate coefficient comparison
Source: general-ring smooth purity, proof (3), tensor compatibility of comparisons.
(blueprint: lem-sp-general-ring-affine-line-step-strength).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
open Etale OrdinaryAffineTensorActions
attribute [local implicit_reducible] affineTraceTower
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance] Sheaf.monoidalCategory
  Etale.isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  Etale.isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor
attribute [local irreducible] Functor.leftDerivedFunctor Etale.upperStar
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  Etale.derivedTensorRight ordinaryFiniteTensorPullback ordinaryFiniteTensorRightMapIso
  Etale.leftDerivedUpperStarTensorIso ordinaryFiniteP1Right
  ordinaryFiniteTwistedPullback

private theorem descent_conjugate
    {C E : Type*} [Category C] [Category E]
    [MonoidalCategory C] [MonoidalCategory E]
    (P : C ⥤ E) {K B B' : C} {V V' W : E}
    (a : W ≅ P.obj K) (l : V ≅ P.obj B) (l' : V' ≅ P.obj B')
    (c : B ⟶ B')
    (p : P.obj (K ⊗ B) ≅ P.obj K ⊗ P.obj B)
    (p' : P.obj (K ⊗ B') ≅ P.obj K ⊗ P.obj B')
    (hn : P.map (K ◁ c) ≫ p'.hom = p.hom ≫ P.obj K ◁ P.map c) :
    (a.hom ⊗ₘ l.hom) ≫ p.inv ≫ P.map (K ◁ c) ≫ p'.hom ≫
        (a.inv ⊗ₘ l'.inv) = W ◁ (l.hom ≫ P.map c ≫ l'.inv) := by
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_assoc]
  rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id, Category.comp_id, id_tensorHom, whiskerLeft_comp, Category.assoc]

private theorem descent_conjugate_of_formula
    {C E : Type*} [Category C] [Category E]
    [MonoidalCategory C] [MonoidalCategory E]
    (P : C ⥤ E) {K B B' : C} {V V' W R R' : E}
    (a : W ≅ P.obj K) (l : V ≅ P.obj B) (l' : V' ≅ P.obj B')
    (c : B ⟶ B')
    (p : P.obj (K ⊗ B) ≅ P.obj K ⊗ P.obj B)
    (p' : P.obj (K ⊗ B') ≅ P.obj K ⊗ P.obj B')
    (r : R ≅ W ⊗ V) (r' : R' ≅ W ⊗ V')
    (d : R ≅ P.obj (K ⊗ B)) (d' : R' ≅ P.obj (K ⊗ B'))
    (hd : d.hom = r.hom ≫ (a.hom ⊗ₘ l.hom) ≫ p.inv)
    (hd' : d'.inv = p'.hom ≫ (a.inv ⊗ₘ l'.inv) ≫ r'.inv)
    (hn : P.map (K ◁ c) ≫ p'.hom = p.hom ≫ P.obj K ◁ P.map c) :
    d.hom ≫ P.map (K ◁ c) ≫ d'.inv =
      r.hom ≫ (W ◁ (l.hom ≫ P.map c ≫ l'.inv)) ≫ r'.inv := by
  rw [hd, hd']
  simp only [Category.assoc]
  rw [reassoc_of% (descent_conjugate P a l l' c p p' hn)]

private theorem strength_normal_form
    {D E : Type*} [Category D] [Category E]
    [MonoidalCategory D] [MonoidalCategory E]
    (J : D ⥤ E) [J.Monoidal] (X Y L Z : D) (a : X ⊗ Y ⟶ Z) :
    Functor.LaxMonoidal.μ J X (Y ⊗ L) ≫ J.map (α_ X Y L).inv ≫
        J.map (a ▷ L) ≫ Functor.OplaxMonoidal.δ J Z L =
      J.obj X ◁ Functor.OplaxMonoidal.δ J Y L ≫
        (α_ (J.obj X) (J.obj Y) (J.obj L)).inv ≫
          ((Functor.LaxMonoidal.μ J X Y ≫ J.map a) ▷ J.obj L) := by
  rw [Functor.Monoidal.map_associator_inv]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [Functor.Monoidal.μ_δ, Category.comp_id, ← comp_whiskerRight]

private theorem strength_conjugate
    {D E : Type*} [Category D] [Category E]
    [MonoidalCategory D] [MonoidalCategory E]
    (J : D ⥤ E) [J.Monoidal] (X Y Z L L' : D)
    (a : X ⊗ Y ⟶ Z) (v : J.obj L ⟶ J.obj L') :
    (J.obj X ◁ (Functor.OplaxMonoidal.δ J Y L ≫ J.obj Y ◁ v ≫
      Functor.LaxMonoidal.μ J Y L')) ≫
        Functor.LaxMonoidal.μ J X (Y ⊗ L') ≫ J.map (α_ X Y L').inv ≫
          J.map (a ▷ L') =
      Functor.LaxMonoidal.μ J X (Y ⊗ L) ≫ J.map (α_ X Y L).inv ≫
        J.map (a ▷ L) ≫ Functor.OplaxMonoidal.δ J Z L ≫
          (J.obj Z ◁ v) ≫ Functor.LaxMonoidal.μ J Z L' := by
  apply (cancel_mono (Functor.OplaxMonoidal.δ J Z L')).mp
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  rw [strength_normal_form J X Y L' Z a,
    reassoc_of% (strength_normal_form J X Y L Z a)]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc]
  rw [← MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def']

private theorem strength_with_tensorators
    {D E : Type*} [Category D] [Category E]
    [MonoidalCategory D] [MonoidalCategory E]
    (J : D ⥤ E) [J.Monoidal]
    (θ : ∀ X Y : D, J.obj (X ⊗ Y) ≅ J.obj X ⊗ J.obj Y)
    (hμ : ∀ X Y, Functor.LaxMonoidal.μ J X Y = (θ X Y).inv)
    (hδ : ∀ X Y, Functor.OplaxMonoidal.δ J X Y = (θ X Y).hom)
    (X Y Z L L' : D) (a : X ⊗ Y ⟶ Z) (v : J.obj L ⟶ J.obj L') :
    (J.obj X ◁ ((θ Y L).hom ≫ J.obj Y ◁ v ≫ (θ Y L').inv)) ≫
      (θ X (Y ⊗ L')).inv ≫ J.map (α_ X Y L').inv ≫ J.map (a ▷ L') =
      (θ X (Y ⊗ L)).inv ≫ J.map (α_ X Y L).inv ≫ J.map (a ▷ L) ≫
        (θ Z L).hom ≫ (J.obj Z ◁ v) ≫ (θ Z L').inv := by
  simpa only [hμ, hδ] using strength_conjugate J X Y Z L L' a v

private theorem strength_with_tensorators_split
    {D E : Type*} [Category D] [Category E]
    [MonoidalCategory D] [MonoidalCategory E]
    (J : D ⥤ E) [J.Monoidal]
    (θ : ∀ X Y : D, J.obj (X ⊗ Y) ≅ J.obj X ⊗ J.obj Y)
    (hμ : ∀ X Y, Functor.LaxMonoidal.μ J X Y = (θ X Y).inv)
    (hδ : ∀ X Y, Functor.OplaxMonoidal.δ J X Y = (θ X Y).hom)
    (X Y W Z L L' : D) (a : X ⊗ Y ⟶ W) (b : W ⟶ Z)
    (v : J.obj L ⟶ J.obj L') :
    (J.obj X ◁ ((θ Y L).hom ≫ J.obj Y ◁ v ≫ (θ Y L').inv)) ≫
      ((θ X (Y ⊗ L')).inv ≫ J.map (α_ X Y L').inv ≫ J.map (a ▷ L')) ≫
        J.map (b ▷ L') =
      ((θ X (Y ⊗ L)).inv ≫ J.map (α_ X Y L).inv ≫ J.map (a ▷ L)) ≫
        J.map (b ▷ L) ≫ ((θ Z L).hom ≫ (J.obj Z ◁ v) ≫ (θ Z L').inv) := by
  simpa only [comp_whiskerRight, Functor.map_comp, Category.assoc] using
    strength_with_tensorators J θ hμ hδ X Y Z L L' (a ≫ b) v

private theorem tensor_map (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' L L' : DerivedCategoryModule A T} (e : K ≅ K') (c : L ≅ L') :
    (ordinaryFiniteTensorRightMapIso A T e c).hom = e.hom ⊗ₘ c.hom := by
  change e.hom ▷ L ≫ K' ◁ c.hom = _
  rw [MonoidalCategory.tensorHom_def]

private theorem tensor_map_inv (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' L L' : DerivedCategoryModule A T} (e : K ≅ K') (c : L ≅ L') :
    (ordinaryFiniteTensorRightMapIso A T e c).inv = e.inv ⊗ₘ c.inv := by
  change K' ◁ c.inv ≫ e.inv ▷ L = _
  rw [MonoidalCategory.tensorHom_def']

private theorem line_descent_hom
    (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hN : (N : A) = 0) (tN : OrdinaryFiniteTwistTransport A N hN)
    (U : Scheme.{u}) (hNU : IsUnit (N : Γ(U, ⊤))) (K : DerivedCategoryModule A U) :
    let j := ProjectiveLine.affineChart U
    let q := ProjectiveLine U ↘ U
    let p := AffineSpace PUnit.{u + 1} U ↘ U
    let a := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j q p
      (ProjectiveLine.affineChart_over U).symm).symm.app K
    let l := ordinaryFiniteShiftedLinePullback A N hN tN j
      (affineTraceProjectiveInvertible N U hNU) ≪≫
        (ordinaryFiniteShiftedLinePullback A N hN tN p hNU).symm
    (affineLinearLineDescent A N hN tN U hNU K).hom =
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K)
        ((ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧)).hom ≫
      (a.hom ⊗ₘ l.hom) ≫
      (ordinaryFiniteTensorPullback A p K
        ((ordinaryFiniteLine A N hN U)⟦(2 : ℤ)⟧)).inv := by
  simp only [affineLinearLineDescent, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    tensor_map]

private theorem line_descent_inv
    (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hN : (N : A) = 0) (tN : OrdinaryFiniteTwistTransport A N hN)
    (U : Scheme.{u}) (hNU : IsUnit (N : Γ(U, ⊤))) (K : DerivedCategoryModule A U) :
    let j := ProjectiveLine.affineChart U
    let q := ProjectiveLine U ↘ U
    let p := AffineSpace PUnit.{u + 1} U ↘ U
    let a := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j q p
      (ProjectiveLine.affineChart_over U).symm).symm.app K
    let l := ordinaryFiniteShiftedLinePullback A N hN tN j
      (affineTraceProjectiveInvertible N U hNU) ≪≫
        (ordinaryFiniteShiftedLinePullback A N hN tN p hNU).symm
    (affineLinearLineDescent A N hN tN U hNU K).inv =
      (ordinaryFiniteTensorPullback A p K
        ((ordinaryFiniteLine A N hN U)⟦(2 : ℤ)⟧)).hom ≫
      (a.inv ⊗ₘ l.inv) ≫
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K)
        ((ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧)).inv := by
  simp only [affineLinearLineDescent, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    tensor_map_inv, Category.assoc]

private theorem tensor_pull_hom (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : DerivedCategoryModule A Y) :
    let _ : (ordinaryFinitePullback A f).Monoidal :=
      Etale.leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) f
    (ordinaryFiniteTensorPullback A f K L).hom =
      Functor.OplaxMonoidal.δ (ordinaryFinitePullback A f) K L := by
  exact (Etale.leftDerivedUpperStarMonoidal_δ (ModuleCat.{u + 1} A) f K L).symm

private theorem tensor_pull_inv (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : DerivedCategoryModule A Y) :
    let : (ordinaryFinitePullback A f).Monoidal :=
      Etale.leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) f
    (ordinaryFiniteTensorPullback A f K L).inv =
      Functor.LaxMonoidal.μ (ordinaryFinitePullback A f) K L := by
  exact (Etale.leftDerivedUpperStarMonoidal_μ (ModuleCat.{u + 1} A) f K L).symm

private theorem descent_form
    (A : Type (u + 1)) [CommRing A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (tM : OrdinaryFiniteTwistTransport A M hM)
    (tN : OrdinaryFiniteTwistTransport A N hN)
    (U : Scheme.{u}) (hMU : IsUnit (M : Γ(U, ⊤)))
    (hNU : IsUnit (N : Γ(U, ⊤)))
    (c : (ordinaryFiniteLine A M hM U)⟦(2 : ℤ)⟧ ⟶
      (ordinaryFiniteLine A N hN U)⟦(2 : ℤ)⟧)
    (K : DerivedCategoryModule A U) :
    let j := ProjectiveLine.affineChart U
    let q := ProjectiveLine U ↘ U
    let p := AffineSpace PUnit.{u + 1} U ↘ U
    let lM := ordinaryFiniteShiftedLinePullback A M hM tM j
      (affineTraceProjectiveInvertible M U hMU) ≪≫
        (ordinaryFiniteShiftedLinePullback A M hM tM p hMU).symm
    let lN := ordinaryFiniteShiftedLinePullback A N hN tN j
      (affineTraceProjectiveInvertible N U hNU) ≪≫
        (ordinaryFiniteShiftedLinePullback A N hN tN p hNU).symm
    (affineLinearLineDescent A M hM tM U hMU K).hom ≫
      (ordinaryFinitePullback A p).map (K ◁ c) ≫
      (affineLinearLineDescent A N hN tN U hNU K).inv =
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K)
        ((ordinaryFiniteLine A M hM (ProjectiveLine U))⟦(2 : ℤ)⟧)).hom ≫
      ((linePull A U).obj K ◁ (lM.hom ≫ (ordinaryFinitePullback A p).map c ≫ lN.inv)) ≫
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K)
        ((ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧)).inv := by
  dsimp only
  let j := ProjectiveLine.affineChart U
  let q := ProjectiveLine U ↘ U
  let p := AffineSpace PUnit.{u + 1} U ↘ U
  let lM := ordinaryFiniteShiftedLinePullback A M hM tM j
    (affineTraceProjectiveInvertible M U hMU) ≪≫
      (ordinaryFiniteShiftedLinePullback A M hM tM p hMU).symm
  let lN := ordinaryFiniteShiftedLinePullback A N hN tN j
    (affineTraceProjectiveInvertible N U hNU) ≪≫
      (ordinaryFiniteShiftedLinePullback A N hN tN p hNU).symm
  exact descent_conjugate_of_formula (ordinaryFinitePullback A p)
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j q p
      (ProjectiveLine.affineChart_over U).symm).symm.app K)
    lM lN c
    (ordinaryFiniteTensorPullback A p K _) (ordinaryFiniteTensorPullback A p K _)
    (ordinaryFiniteTensorPullback A j _ _) (ordinaryFiniteTensorPullback A j _ _)
    (affineLinearLineDescent A M hM tM U hMU K)
    (affineLinearLineDescent A N hN tN U hNU K)
    (line_descent_hom A M hM tM U hMU K)
    (line_descent_inv A N hN tN U hNU K)
    (Etale.leftDerivedUpperStarTensorIso_hom_naturality_right (g := p) K c)

private theorem line_step_form
    (A : Type (u + 1)) [CommRing A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (tM : OrdinaryFiniteTwistTransport A M hM)
    (tN : OrdinaryFiniteTwistTransport A N hN)
    (T : Scheme.{u}) (hMunit : IsUnit (M : Γ(T, ⊤)))
    (hNunit : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN) (d : ℕ)
    (K : DerivedCategoryModule A (affineTraceTower T d)) :
    let U := affineTraceTower T d
    let j := ProjectiveLine.affineChart U
    let q := ProjectiveLine U ↘ U
    let p := AffineSpace PUnit.{u + 1} U ↘ U
    let lM := ordinaryFiniteShiftedLinePullback A M hM tM j
      (affineTraceProjectiveInvertible M U (affineTraceInvertible M T hMunit d)) ≪≫
        (ordinaryFiniteShiftedLinePullback A M hM tM p
          (affineTraceInvertible M T hMunit d)).symm
    let lN := ordinaryFiniteShiftedLinePullback A N hN tN j
      (affineTraceProjectiveInvertible N U (affineTraceInvertible N T hNunit d)) ≪≫
        (ordinaryFiniteShiftedLinePullback A N hN tN p
          (affineTraceInvertible N T hNunit d)).symm
    let v := lM.hom ≫ (ordinaryFinitePullback A p).map
      (finiteGeneralRingShiftedStageComparison A M N hM hN tM tN T
        hMunit hNunit b d).hom ≫ lN.inv
    finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMunit hNunit b d K =
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K)
        ((ordinaryFiniteLine A M hM (ProjectiveLine U))⟦(2 : ℤ)⟧)).hom ≫
      ((linePull A U).obj K ◁ v) ≫
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K)
        ((ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧)).inv := by
  exact descent_form A M N hM hN tM tN (affineTraceTower T d)
    (affineTraceInvertible M T hMunit d) (affineTraceInvertible N T hNunit d)
    (finiteGeneralRingShiftedStageComparison A M N hM hN tM tN T
      hMunit hNunit b d).hom K

private theorem line_strength_hom
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : (N : A) = 0)
    (U : Scheme.{u}) (K H : DerivedCategoryModule A U) :
    let j := ProjectiveLine.affineChart U
    let q := ProjectiveLine U ↘ U
    let L := (ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧
    (lineStrength A N hN U K H).hom =
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K)
        (((ordinaryFinitePullback A q).obj H) ⊗ L)).inv ≫
      (ordinaryFinitePullback A j).map
        (α_ ((ordinaryFinitePullback A q).obj K) ((ordinaryFinitePullback A q).obj H) L).inv ≫
      (ordinaryFinitePullback A j).map ((ordinaryFiniteTensorPullback A q K H).inv ▷ L) := by
  simp only [lineStrength, properStrength, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensor_map, Iso.refl_hom, tensorHom_id, Functor.map_comp,
    Etale.derivedTensorAssociator, ordinaryFiniteP1Right, ordinaryFiniteTwistedPullback,
    Functor.comp_obj, Etale.derivedTensorRight, Etale.derivedTensor,
    Functor.flip_obj_obj, curriedTensor_obj_obj]

private theorem line_right_map
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : (N : A) = 0)
    (U : Scheme.{u}) {K H : DerivedCategoryModule A U} (f : K ⟶ H) :
    (affineTraceLineRight A N hN U).map f =
      (ordinaryFinitePullback A (ProjectiveLine.affineChart U)).map
        ((ordinaryFinitePullback A (ProjectiveLine U ↘ U)).map f ▷
          (ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧) := by
  rfl

private theorem line_strength_conjugate
    (A : Type (u + 1)) [CommRing A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0) (U : Scheme.{u})
    (v : (ordinaryFinitePullback A (ProjectiveLine.affineChart U)).obj
        ((ordinaryFiniteLine A M hM (ProjectiveLine U))⟦(2 : ℤ)⟧) ⟶
      (ordinaryFinitePullback A (ProjectiveLine.affineChart U)).obj
        ((ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧))
    (K H Z : DerivedCategoryModule A U)
    (u : ((ordinaryFiniteTensor A U).obj K).obj H ⟶ Z) :
    let e (Y : DerivedCategoryModule A U) :=
      (ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart U)
        ((ordinaryFinitePullback A (ProjectiveLine U ↘ U)).obj Y)
        ((ordinaryFiniteLine A M hM (ProjectiveLine U))⟦(2 : ℤ)⟧)).hom ≫
      ((linePull A U).obj Y ◁ v) ≫
      (ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart U)
        ((ordinaryFinitePullback A (ProjectiveLine U ↘ U)).obj Y)
        ((ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧)).inv
    ((ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} U)).obj
      ((linePull A U).obj K)).map (e H) ≫
      (lineStrength A N hN U K H).hom ≫ (affineTraceLineRight A N hN U).map u =
      (lineStrength A M hM U K H).hom ≫ (affineTraceLineRight A M hM U).map u ≫ e Z := by
  dsimp only
  let j := ProjectiveLine.affineChart U
  let q := ProjectiveLine U ↘ U
  let : (ordinaryFinitePullback A j).Monoidal :=
    Etale.leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) j
  have h := strength_with_tensorators_split (ordinaryFinitePullback A j)
    (ordinaryFiniteTensorPullback A j)
    (fun X Y ↦ (tensor_pull_inv A j X Y).symm)
    (fun X Y ↦ (tensor_pull_hom A j X Y).symm)
    ((ordinaryFinitePullback A q).obj K) ((ordinaryFinitePullback A q).obj H)
    ((ordinaryFinitePullback A q).obj (((ordinaryFiniteTensor A U).obj K).obj H))
    ((ordinaryFinitePullback A q).obj Z)
    ((ordinaryFiniteLine A M hM (ProjectiveLine U))⟦(2 : ℤ)⟧)
    ((ordinaryFiniteLine A N hN (ProjectiveLine U))⟦(2 : ℤ)⟧)
    (ordinaryFiniteTensorPullback A q K H).inv ((ordinaryFinitePullback A q).map u) v
  rw [line_strength_hom, line_strength_hom, line_right_map, line_right_map]
  exact h

/-- The explicitly descended coefficient comparison respects the specified right
strength, including the right unitor at the coefficient unit. This is an identity of
right-functor comparisons, independent of adjunctions and trace normalizations.

Source: general-ring smooth purity, proof (3), factorwise tensor compatibility;
affine-space top-trace proof, last paragraph.
(blueprint: lem-sp-general-ring-affine-line-step-strength).

Proof: expand lineStrength into tensor inverse image on the open chart and the
projective strength. Expand the latter into inverse associativity followed by tensor
inverse image on the projective projection. Expand each lineStep into line descent,
the map on the shifted line factor, and inverse target descent. Naturality of tensor
inverse image moves that shifted-line map through the two tensorators. Tensor
interchange cancels the inverse-image composition comparison against its inverse,
leaving conjugation by the chart tensorator. Monoidality of chart inverse image
rewrites strength into associator normal form. Associator naturality and tensor
interchange give the identity, also after the map of the right unitor.
These are identities before applying any left functor or counit; they hold also for
the zero ring, the empty scheme, d=0 and arbitrary unbounded K.
-/
theorem finiteGeneralRingAffineLineStep_strength
    (A : Type (u + 1)) [CommRing A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (tM : OrdinaryFiniteTwistTransport A M hM)
    (tN : OrdinaryFiniteTwistTransport A N hN)
    (T : Scheme.{u}) (hMunit : IsUnit (M : Γ(T, ⊤)))
    (hNunit : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN) (d : ℕ)
    (K : DerivedCategoryModule A (affineTraceTower T d)) :
    let U := affineTraceTower T d
    let one := ordinaryFiniteUnit A U
    let e := finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMunit hNunit b d
    ((ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} U)).obj
        ((linePull A U).obj K)).map (e one) ≫
      (lineStrength A N hN U K one).hom ≫
      (affineTraceLineRight A N hN U).map (derivedTensorSingleUnitIso K).hom =
    (lineStrength A M hM U K one).hom ≫
      (affineTraceLineRight A M hM U).map (derivedTensorSingleUnitIso K).hom ≫ e K := by
  dsimp only
  let U := affineTraceTower T d
  let j := ProjectiveLine.affineChart U
  let p := AffineSpace PUnit.{u + 1} U ↘ U
  let one := ordinaryFiniteUnit A U
  let lM := ordinaryFiniteShiftedLinePullback A M hM tM j
    (affineTraceProjectiveInvertible M U (affineTraceInvertible M T hMunit d)) ≪≫
      (ordinaryFiniteShiftedLinePullback A M hM tM p
        (affineTraceInvertible M T hMunit d)).symm
  let lN := ordinaryFiniteShiftedLinePullback A N hN tN j
    (affineTraceProjectiveInvertible N U (affineTraceInvertible N T hNunit d)) ≪≫
      (ordinaryFiniteShiftedLinePullback A N hN tN p
        (affineTraceInvertible N T hNunit d)).symm
  let v := lM.hom ≫ (ordinaryFinitePullback A p).map
    (finiteGeneralRingShiftedStageComparison A M N hM hN tM tN T
      hMunit hNunit b d).hom ≫ lN.inv
  rw [line_step_form, line_step_form]
  exact line_strength_conjugate A M N hM hN U v K one K
    (derivedTensorSingleUnitIso K).hom

end AlgebraicGeometry.ProEtale
