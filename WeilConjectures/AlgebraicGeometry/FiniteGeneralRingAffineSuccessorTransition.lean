/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingAffineLineStep


/-! # Last-coordinate factorization of the finite-ring transition
Source: general-ring smooth purity, proof (3), ordered affine induction.
(blueprint: lem-sp-general-ring-affine-successor-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
open Etale
attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  affineLinearBaseCoefficient Etale.derivedTensorRight
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem line_descent_map
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    {K K' : DerivedCategoryModule A S} (f : K ⟶ K') :
    (affineTraceLineRight A N hA S).map f ≫
      (affineLinearLineDescent A N hA t S hS K').hom =
    (affineLinearLineDescent A N hA t S hS K).hom ≫
      (ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} S ↘ S)).map
        (f ▷ ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)) := by
  have h := line_descent_naturality A N N hA hA t t S hS hS K K' f
    (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp)
  simpa only [tensorHom_id, affineTraceLineRight, ordinaryFiniteP1Right,
    ordinaryFiniteTwistedPullback, Functor.comp_map, Etale.derivedTensorRight,
    Functor.flip_obj_map, Etale.derivedTensor_map_app] using h

/-- The canonical successor transition is the comparison on its last coordinate
followed by the preceding transition. No counit, Kummer compatibility, or induction
hypothesis is needed for this tensor identity.

Source: general-ring smooth purity, proof (3), ordered tensor induction.
(blueprint: lem-sp-general-ring-affine-successor-transition).

Proof: expand the successor coefficient descent. Its middle arrow tensors the
preceding descent with inverse shifted-line pullback. Tensor inverse-image naturality
moves the level-power comparison through this arrow, and inverse-image composition
naturality moves it through the final composition comparison. Line-descent naturality
moves the preceding transition through the last line functor. Cancel the target
successor descent, giving exactly the displayed factorization. -/
theorem finiteGeneralRingAffineSuccessorTransition
    (A : Type (u + 1)) [CommRing A]
    (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (T : Scheme.{u})
    (hMunit : IsUnit (M : Γ(T, ⊤))) (hNunit : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (d : ℕ)
    (eD : (Etale.affineTraceRight A M hM T d).obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hN T d).obj
        (Etale.ordinaryFiniteUnit A T))
    (heD : eD =
      (Etale.affineLinearCoefficientDescent A M hM tM T hMunit d).hom ≫
        (Etale.ordinaryFinitePullback A (affineTraceProjection T d)).map
          (finiteGeneralRingLevelPower A M N hM hN T b d).hom ≫
        (Etale.affineLinearCoefficientDescent A N hN tN T hNunit d).inv)
    (eSucc : (Etale.affineTraceRight A M hM T (d + 1)).obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hN T (d + 1)).obj
        (Etale.ordinaryFiniteUnit A T))
    (heSucc : eSucc =
      (Etale.affineLinearCoefficientDescent A M hM tM T hMunit (d + 1)).hom ≫
        (Etale.ordinaryFinitePullback A (affineTraceProjection T (d + 1))).map
          (finiteGeneralRingLevelPower A M N hM hN T b (d + 1)).hom ≫
        (Etale.affineLinearCoefficientDescent A N hN tN T hNunit (d + 1)).inv)
 :
    eSucc =
      finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMunit hNunit b d
        ((affineTraceRight A M hM T d).obj (ordinaryFiniteUnit A T)) ≫
      (affineTraceLineRight A N hN (affineTraceTower T d)).map eD := by
  let X := affineTraceTower T d
  let p := affineTraceProjection T d
  let q := AffineSpace PUnit.{u + 1} X ↘ X
  let P := ordinaryFinitePullback A p
  let Q := ordinaryFinitePullback A q
  let Ks := (affineTraceRight A M hM T d).obj (ordinaryFiniteUnit A T)
  let Kr := (affineTraceRight A N hN T d).obj (ordinaryFiniteUnit A T)
  let Bs := affineLinearBaseCoefficient A M hM T d
  let Br := affineLinearBaseCoefficient A N hN T d
  let Ls := (ordinaryFiniteLine A M hM T)⟦(2 : ℤ)⟧
  let Lr := (ordinaryFiniteLine A N hN T)⟦(2 : ℤ)⟧
  let es := affineLinearCoefficientDescent A M hM tM T hMunit d
  let er := affineLinearCoefficientDescent A N hN tN T hNunit d
  let cs := ordinaryFiniteShiftedLinePullback A M hM tM p hMunit
  let cr := ordinaryFiniteShiftedLinePullback A N hN tN p hNunit
  let bD : Bs ≅ Br := finiteGeneralRingLevelPower A M N hM hN T b d
  let c : Ls ⟶ Lr := ((shiftFunctor (DerivedCategoryModule A T) (2 : ℤ)).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso b)).hom
  let v := (finiteGeneralRingShiftedStageComparison A M N hM hN tM tN T
    hMunit hNunit b d).hom
  let αs := (es.hom ⊗ₘ cs.inv) ≫ (ordinaryFiniteTensorPullback A p Bs Ls).inv
  let αr := (er.hom ⊗ₘ cr.inv) ≫ (ordinaryFiniteTensorPullback A p Br Lr).inv
  have hz : eD ≫ er.hom = es.hom ≫ P.map bD.hom := by
    rw [heD]
    simp only [P, es, er, bD, Category.assoc, Iso.inv_hom_id, Category.comp_id, p]
  have hc : v ≫ cr.inv = cs.inv ≫ P.map c := by
    simp only [v, finiteGeneralRingShiftedStageComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id, cs, cr, P, c, p]
  have ht : (eD ⊗ₘ v) ≫ αr = αs ≫ P.map (bD.hom ⊗ₘ c) :=
    inverse_tensor_descent_square P es er cs cr
      (ordinaryFiniteTensorPullback A p Bs Ls) (ordinaryFiniteTensorPullback A p Br Lr)
      bD.hom c eD v hz hc
      (Etale.leftDerivedUpperStarTensorComparison_naturality (ModuleCat.{u + 1} A) p _ _)
  have hm : Q.map (P.map (bD.hom ⊗ₘ c)) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.app (Br ⊗ Lr) =
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.app (Bs ⊗ Ls) ≫
      (ordinaryFinitePullback A (q ≫ p)).map (bD.hom ⊗ₘ c) := by
    exact (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.naturality
      (bD.hom ⊗ₘ c)
  have hn := line_descent_map A N hN tN X (affineTraceInvertible N T hNunit d) eD
  have hl :
      (finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMunit hNunit b d Ks ≫
        (affineTraceLineRight A N hN X).map eD) ≫
          (affineLinearLineDescent A N hN tN X
            (affineTraceInvertible N T hNunit d) Kr).hom =
      (affineLinearLineDescent A M hM tM X
        (affineTraceInvertible M T hMunit d) Ks).hom ≫ Q.map (eD ⊗ₘ v) := by
    simp only [finiteGeneralRingAffineLineStep, ordinaryFiniteTensor,
      Etale.derivedTensor_obj_map, Category.assoc]
    dsimp only [X, Ks] at hn ⊢
    rw [hn]
    simp only [Iso.inv_hom_id_assoc]
    dsimp only [Q, q, X]
    rw [← Functor.map_comp]
    congr 1
    simpa only [Q, q, X, Ks, v] using
      congrArg Q.map (tensorHom_def' eD v).symm
  apply (cancel_mono
    (affineLinearCoefficientDescent A N hN tN T hNunit (d + 1)).hom).mp
  have hsucc : (finiteGeneralRingLevelPower A M N hM hN T b (d + 1)).hom =
      bD.hom ⊗ₘ c := by
    exact tensor_iso_hom A T bD
      ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso b))
  rw [heSucc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hsucc]
  let dr := (affineLinearLineDescent A N hN tN X
    (affineTraceInvertible N T hNunit d) Kr).hom
  let ds := (affineLinearLineDescent A M hM tM X
    (affineTraceInvertible M T hMunit d) Ks).hom
  let mr := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.app (Br ⊗ Lr)
  let ms := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.app (Bs ⊗ Ls)
  have hR : (affineLinearCoefficientDescent A N hN tN T hNunit (d + 1)).hom =
      dr ≫ Q.map αr ≫ mr := tower_descent_succ_hom A N hN tN T hNunit d
  have hS : (affineLinearCoefficientDescent A M hM tM T hMunit (d + 1)).hom =
      ds ≫ Q.map αs ≫ ms := tower_descent_succ_hom A M hM tM T hMunit d
  have hp := paste_descent_successor Q
    (finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMunit hNunit b d Ks)
    ((affineTraceLineRight A N hN X).map eD)
    (finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMunit hNunit b d Ks ≫
      (affineTraceLineRight A N hN X).map eD)
    dr ds (eD ⊗ₘ v) αr αs (P.map (bD.hom ⊗ₘ c)) mr ms
    ((ordinaryFinitePullback A (q ≫ p)).map (bD.hom ⊗ₘ c))
    (affineLinearCoefficientDescent A N hN tN T hNunit (d + 1)).hom
    (affineLinearCoefficientDescent A M hM tM T hMunit (d + 1)).hom
    hR hS rfl hl ht hm
  simpa only [X, q, p, Ks, Br, Lr, affineTraceProjection,
    affineLinearBaseCoefficient, Category.assoc] using hp.symm

end AlgebraicGeometry.ProEtale
