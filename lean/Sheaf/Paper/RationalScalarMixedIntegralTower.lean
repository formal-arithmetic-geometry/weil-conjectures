/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Paper.RationalScalarCompletionUnitSquare

/-! # Integral mixed coefficient-tower cancellation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable (g : X ⟶ Y)
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

private theorem mixed_inverse_square {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {A B : C} {U V W : D}
    (e : A ≅ B) (f : U ≅ T.obj A) (q : V ≅ W)
    (a : T.obj B ⟶ W) (b : U ⟶ V)
    (h : f.hom ≫ T.map e.hom ≫ a = b ≫ q.hom) :
    T.map e.inv ≫ f.inv ≫ b = a ≫ q.inv := by
  apply (cancel_epi (T.map e.hom)).1
  apply (cancel_epi f.hom).1
  have ht := congrArg (fun k ↦ k ≫ q.inv) h
  simpa only [Category.assoc, ← T.map_comp_assoc, Iso.hom_inv_id,
    T.map_id, Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc] using ht.symm

/-- The specified strict integral scalar comparisons respect coefficient towers.
Source: BS Remark 6.8.15; Stacks 0D6D.
(blueprint: lem-per-mixed-integral-coefficient-tower).

Proof: invert the reflected coefficient-tower equation. Conjugate by the ambient
completion comparisons. Naturality moves the final comparison past the scalar
associator, the two middle comparisons cancel, and naturality of the scalar
associator moves the initial comparison to the other route. -/
theorem rationalMixedIntegralCoefficientTower
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l F G j X).map
        ((rationalScalarStrictBeta l E F i g).hom.app K) ≫
      (rationalScalarStrictBeta l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcActualStrictCompletedPull (pbcIntegralDatum l G) g).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) =
    (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K) ≫
      (rationalScalarStrictBeta l E G (j.comp i) g).hom.app K := by
  let C := pbcEmbeddingAmbientTensor l F G j X
  let B := pbcActualCompletedPull g (pbcIntegralDatum l G)
  let eE := pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l E) g
  let eF := pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l F) g
  let eG := pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l G) g
  let bEF := rationalScalarReflectedBeta l E F i g
  let bFG := rationalScalarReflectedBeta l F G j g
  let bEG := rationalScalarReflectedBeta l E G (j.comp i) g
  let cX := pbcAmbientScalarComp l E F G i j X
  let cY := pbcAmbientScalarComp l E F G i j Y
  have hr : C.map (bEF.hom.app K) ≫
      bFG.hom.app ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      B.map (cY.hom.app K) =
    cX.hom.app ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) ≫
      bEG.hom.app K := by
    exact mixed_inverse_square C
      ((pbcScalarCompletedPullIso l E F i g).app K)
      ((pbcScalarCompletedPullIso l F G j g).app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K))
      ((pbcScalarCompletedPullIso l E G (j.comp i) g).app K)
      (cX.hom.app ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K))
      (B.map (cY.hom.app K))
      (rationalScalarCompletionUnitSquare_coefficients l E F i g G j K)
  have hn : eG.inv.app ((pbcEmbeddingAmbientTensor l F G j Y).obj
      ((pbcEmbeddingAmbientTensor l E F i Y).obj K)) ≫
      (pbcActualStrictCompletedPull (pbcIntegralDatum l G) g).map (cY.hom.app K) =
    B.map (cY.hom.app K) ≫
      eG.inv.app ((pbcEmbeddingAmbientTensor l E G (j.comp i) Y).obj K) :=
    (eG.inv.naturality (cY.hom.app K)).symm
  have ha : C.map ((pbcEmbeddingAmbientTensor l E F i X).map (eE.hom.app K)) ≫
      cX.hom.app ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) =
    cX.hom.app ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K) ≫
      (pbcEmbeddingAmbientTensor l E G (j.comp i) X).map (eE.hom.app K) :=
    cX.hom.naturality (eE.hom.app K)
  simp only [rationalScalarStrictBeta, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  change C.map ((pbcEmbeddingAmbientTensor l E F i X).map (eE.hom.app K)) ≫
    C.map (bEF.hom.app K) ≫ C.map (eF.inv.app _) ≫
    C.map (eF.hom.app _) ≫ bFG.hom.app _ ≫ eG.inv.app _ ≫
    (pbcActualStrictCompletedPull (pbcIntegralDatum l G) g).map (cY.hom.app K) =
    cX.hom.app _ ≫ (pbcEmbeddingAmbientTensor l E G (j.comp i) X).map
      (eE.hom.app K) ≫ bEG.hom.app K ≫ eG.inv.app _
  erw [(eF.app ((pbcEmbeddingAmbientTensor l E F i Y).obj K)).map_inv_hom_id_assoc C]
  erw [hn, reassoc_of% hr, reassoc_of% ha]
  rfl


end AlgebraicGeometry.Scheme
