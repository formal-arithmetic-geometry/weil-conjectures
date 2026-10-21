/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps
import Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Sheaf.SixFunctors.TensorProjectionAdjunct
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Cancelling the positive twist in the projective-line splitting

Source: the final tensor-projection sentence of thm-amb-p1-decomposition.proof.md
(blueprint: lem-asd-ordinary-finite-p1-untwist).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize


private theorem descIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} {X' Y' Z' : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) [IsIso (biprod.desc a b)]
    (e : F.obj X ≅ X') (e' : F.obj Y ≅ Y') (v : F.obj Z ≅ Z') :
    IsIso (biprod.desc (e.inv ≫ F.map a ≫ v.hom) (e'.inv ≫ F.map b ≫ v.hom)) := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let q := biprod.mapIso e.symm e'.symm ≪≫ (Functor.mapBiprod F X Y).symm ≪≫
    F.mapIso (asIso (biprod.desc a b)) ≪≫ v
  have h : q.hom = biprod.desc (e.inv ≫ F.map a ≫ v.hom)
      (e'.inv ≫ F.map b ≫ v.hom) := by
    apply biprod.hom_ext' <;>
      simp [q, ← Functor.map_comp_assoc]
  rw [← h]
  infer_instance

private theorem untwistIsIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D) (K L U : C) (E V : D)
    [(P.obj K).Additive]
    (delta : ∀ M, F.obj ((P.obj K).obj M) ⟶ (Q.obj (F.obj K)).obj (F.obj M))
    (proj : (P.obj K).obj (G.obj E) ⟶ G.obj ((Q.obj (F.obj K)).obj E)) [IsIso proj]
    (hproj : ∀ (M : C) (a : M ⟶ G.obj E),
      (adj.homEquiv _ _).symm ((P.obj K).map a ≫ proj) =
        delta M ≫ (Q.obj (F.obj K)).map ((adj.homEquiv _ _).symm a))
    (e : (P.obj K).obj L ≅ U) (r : (P.obj K).obj U ≅ K)
    (u : F.obj U ≅ V) (l : F.obj L ≅ E)
    (w : (Q.obj (F.obj K)).obj E ≅ V)
    (r' : (Q.obj (F.obj K)).obj V ≅ F.obj K)
    (he : F.map e.hom ≫ u.hom =
      delta L ≫ (Q.obj (F.obj K)).map l.hom ≫ w.hom)
    (hr : F.map r.inv ≫ delta U ≫ (Q.obj (F.obj K)).map u.hom = r'.inv)
    (c : V ⟶ E)
    (hb : IsIso (biprod.desc (adj.homEquiv _ _ l.hom)
      (adj.homEquiv _ _ (u.hom ≫ c)))) :
    IsIso (biprod.desc (adj.homEquiv _ _ u.hom)
      (adj.homEquiv _ _ (r'.inv ≫ (Q.obj (F.obj K)).map c ≫ w.hom))) := by
  let a := adj.homEquiv _ _ l.hom
  let b := adj.homEquiv _ _ (u.hom ≫ c)
  let v := asIso proj ≪≫ G.mapIso w
  have trans (M : C) (z : M ⟶ G.obj E) :
      (adj.homEquiv _ _).symm ((P.obj K).map z ≫ v.hom) =
        delta M ≫ (Q.obj (F.obj K)).map ((adj.homEquiv _ _).symm z) ≫ w.hom := by
    dsimp only [v, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm, hproj]
    simp only [Category.assoc]
  have ha : e.inv ≫ (P.obj K).map a ≫ v.hom = adj.homEquiv _ _ u.hom := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm, trans]
    simp only [a, Equiv.symm_apply_apply]
    rw [← he]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  have hb' : r.inv ≫ (P.obj K).map b ≫ v.hom =
      adj.homEquiv _ _ (r'.inv ≫ (Q.obj (F.obj K)).map c ≫ w.hom) := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm, trans]
    simp only [b, Equiv.symm_apply_apply, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hr]
  have := descIso (P.obj K) a b e r v
  rw [ha, hb'] at this
  exact this

private theorem evaluation_isIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    IsIso (p1DecompositionEvaluation A N hN hA T hT) := by
  have hv : IsIso ((ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
      (ordinaryFiniteConstant A T)) := by
    change IsIso ((ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
      (Scheme.finiteEtaleTateSheaf A N T hA 0))
    rw [← p1DecompositionSheafProduct_hom A N hN hA T hT]
    infer_instance
  unfold p1DecompositionEvaluation p1DecompositionDegreeZeroEvaluation
  infer_instance

/-- Tensoring the normalized positive-twist splitting with the inverse line gives
exactly the unit and Chern-evaluation splitting. No Noetherian hypothesis is needed:
the source library's finite-coefficient proper projection formula is unbounded and
holds over every base.
Source: main-20261015, thm-amb-p1-decomposition.proof.md, final sentence
(blueprint: lem-asd-ordinary-finite-p1-untwist).

Proof: put K=A(-1)[-2] and L=A(1)[2]. The normalized product identifies K tensor L
with A, and identifies its pullback tensor L_P with A_P. Tensor the given splitting
with K, use preservation of binary biproducts, then apply the canonical proper
projection formula for q and the direct image of evaluation. Every map is an
isomorphism. Normalized positive transports agree by their roots and pure-tensor
equations. Apply tensorProjectionAdjunct to each of the two components. For the
first component the adjunction triangle gives the identity after twist pullback;
compatibility of evaluation with inverse image identifies its adjoint with the
constant comparison. For the second, counit naturality gives tensoring with c
followed by evaluation, with the canonical right-unit comparison. These are precisely
the two adjuncts defining p1DecompositionMap. The shifts are even, so the signed
symmetry introduces no extra sign. The argument uses invertibility of N to make the
finite root line invertible, and permits A=0, N=1, or the empty base. -/
theorem isIso_p1DecompositionMap_of_twisted
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hb : IsIso (biprod.desc (ordinaryFiniteP1Unit A N hA t S hS)
      (ordinaryFiniteP1ChernPushforward A N hA S c))) :
    IsIso (p1DecompositionMap A N hN hA S hS c) := by
  let q := ProjectiveLine S ↘ S
  let K := p1DecompositionTwist A N hA S (-1) (-2)
  let L := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧
  let E := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  have : IsProper q := ProjectiveSpace.instIsProper (ULift.{u} (Fin 2)) S
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A q
  have hp : IsIso (ordinaryFiniteProjection A q E K) := by
    unfold ordinaryFiniteProjection
    infer_instance
  have := evaluation_isIso A N hN hA S hS
  have := evaluation_isIso A N hN hA (ProjectiveLine S)
    ((map_natCast q.appTop.hom N) ▸ hS.map q.appTop.hom)
  let w : ((ordinaryFiniteTensor A (ProjectiveLine S)).obj
      ((ordinaryFinitePullback A q).obj K)).obj E ≅
        ordinaryFiniteUnit A (ProjectiveLine S) :=
    ((ordinaryFiniteTensor A (ProjectiveLine S)).mapIso
      (p1DecompositionTwistPullback A N hN hA q hS (-1) (-2))).app E ≪≫
      asIso (p1DecompositionEvaluation A N hN hA (ProjectiveLine S)
        ((map_natCast q.appTop.hom N) ▸ hS.map q.appTop.hom))
  obtain ⟨he, hr⟩ := finiteTwistDerivedEvaluation_pullback A N hN hA t q hS
  have : ((ordinaryFiniteTensor A S).obj K).Additive :=
    additive_derivedTensor_obj K
  have h := untwistIsIso (ordinaryFinitePullback A q) (ordinaryFinitePushforward A q)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (ordinaryFiniteTensor A S) (ordinaryFiniteTensor A (ProjectiveLine S)) K L
    (ordinaryFiniteUnit A S) E (ordinaryFiniteUnit A (ProjectiveLine S))
    (fun M => ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) q).app K).app M)
    (ordinaryFiniteProjection A q E K)
    (fun M a => tensorProjectionAdjunct A q K M E a)
    (asIso (p1DecompositionEvaluation A N hN hA S hS))
    (derivedTensorSingleUnitIso K) (ordinaryFiniteUnitPullback A q)
    (ordinaryFiniteShiftedLinePullback A N hA t q hS) w
    (derivedTensorSingleUnitIso ((ordinaryFinitePullback A q).obj K)) he (hr K) c
    (by simpa only [ordinaryFiniteP1Unit, ordinaryFiniteP1ChernPushforward,
      Adjunction.homEquiv_apply, K, L, E, q, Functor.id_obj,
      ordinaryFinitePushforward] using hb)
  simpa only [p1DecompositionMap, p1DecompositionUnit, p1DecompositionChernAdjoint,
    p1DecompositionTensorAdjoint, w, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Category.assoc, K, L, E, q,
    ordinaryFinitePushforward,
    ordinaryFinitePullback, ordinaryFiniteTensor] using h

end AlgebraicGeometry.Etale
