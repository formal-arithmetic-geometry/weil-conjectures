/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z8
-/
module

public import Sheaf.Paper.SemilinearDerivedCalculus
import Sheaf.Paper.SystemTensorReductionFormula
import Sheaf.Paper.SemilinearSingletonEvaluationMate
import Sheaf.CategoryTheory.SystemSingleDerivedExtension
import Sheaf.CategoryTheory.SystemEvaluationTopos
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Composition of the normalized scalar/tensor comparison

Source: Zheng Construction 4.1, Proposition 4.17; Stacks 03EK, 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem evaluation_rightAdjoint (n : ℕ) :
    (e.{c, v, max c v r} J B τ n).IsRightAdjoint := by
  let R := rings.{c, v, max c v r} J B τ
  let E := SheafOfModules.strictSystemSequenceEquivalence R
  have : E.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : E.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let S : SheafOfModules.SystemScalarAssignment.{c, v, max c v r} (J := J) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let T := SheafOfModules.systemTensorCoherence S
  let d := SheafOfModules.systemSingleDerivedExtension R n S T
  have := evaluationAdditive.{c, v, max c v r} J B τ n
  have := evaluationLimits.{c, v, max c v r} J B τ n
  have := evaluationColimits.{c, v, max c v r} J B τ n
  let η : E.inverse ⋙ SheafOfModules.systemEvaluation R n ≅
      evaluation.{c, v, max c v r} J B τ n :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let β := (Functor.mapDerivedCategoryCompIso E.inverse
      (SheafOfModules.systemEvaluation R n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso η
  exact ((d.adjunction.comp E.mapDerivedCategory.toAdjunction).ofNatIsoRight β).isRightAdjoint

private theorem tensor_reduction_precompose (A : Data.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) (K L : D.{c, v, max c v r} J (B m))
    (P Q : DS.{c, v, max c v r} J B τ)
    (p : K ⟶ (e.{c, v, max c v r} J B τ m).obj P)
    (q : L ⟶ (e.{c, v, max c v r} J B τ m).obj Q) :
    (A.scalar h).T.map ((A.levelClosed m).tensor.map (Prod.mkHom p q) ≫
        (A.tensorEvaluation m).inv.app (P, Q)) ≫
      reduction J B τ h (A.scalar h) (A.closed.tensor.obj (P, Q)) ≫
      (A.tensorEvaluation n).hom.app (P, Q) =
    (A.scalarTensor h).hom.app (K, L) ≫
      (A.levelClosed n).tensor.map
        (Prod.mkHom ((A.scalar h).T.map p ≫ reduction J B τ h (A.scalar h) P)
          ((A.scalar h).T.map q ≫ reduction J B τ h (A.scalar h) Q)) := by
  rw [tensor_reduction_formula.{c, v, r} J B τ A P Q h]
  simp only [Functor.map_comp, Category.assoc]
  have hv : (A.scalar h).T.map ((A.tensorEvaluation m).inv.app (P, Q)) ≫
      (A.scalar h).T.map ((A.tensorEvaluation m).hom.app (P, Q)) = 𝟙 _ := by
    rw [← (A.scalar h).T.map_comp, Iso.inv_hom_id_app, (A.scalar h).T.map_id]
  rw [reassoc_of% hv]
  have hn := (A.scalarTensor h).hom.naturality (Prod.mkHom p q)
  change (A.scalar h).T.map ((A.levelClosed m).tensor.map (Prod.mkHom p q)) ≫
      (A.scalarTensor h).hom.app (_, _) =
    (A.scalarTensor h).hom.app (K, L) ≫
      (A.levelClosed n).tensor.map
        (Prod.mkHom ((A.scalar h).T.map p) ((A.scalar h).T.map q)) at hn
  rw [reassoc_of% hn, ← (A.levelClosed n).tensor.map_comp]
  rfl

/-- Scalar/tensor comparison commutes with the specified scalar associator.
Source: blueprint `sk-lem-sp-tower-bound-operations.proof.md` (2), tensor associativity;
Zheng Construction 4.1, Proposition 4.17; Stacks 03EK, 06YY and 07A6.
(blueprint: lem-sp-semilinear-scalar-tensor-composition).

Proof: resolve both inputs by K-flat complexes with flat terms, using the recorded
level tensor models. The scalar models compute derived extension on these complexes;
scalarTensorModel computes its tensor comparison on each signed total summand. The
ordinary_pure formula sends the scalar extension of x tensor y to the tensor of the
two scalar extensions. For r to m to n, both paths therefore send each generalized
pure tensor to the same balanced tensor over B_n. The scalar associator is precisely
this association map: scalarComposition_transpose characterizes it uniquely by the
identity-on-sections restrictionComposition and the actual scalar adjunctions.
Balancing, sheafification, and the total-summand universal property give equality of
chain maps. The derived equations in scalarTensorModel transport that equality to
localized morphisms. Naturality along the resolving quasi-isomorphisms gives the
formula for the original inputs. All coefficient maps may be nonflat. Equal indices
use the same transpose normalization and require no separate choices of unitors. -/
theorem scalarTensor_composition (A : Data.{c, v, r} J B τ)
    {s m n : ℕ} (h : n ≤ m) (k : m ≤ s)
    (K L : D.{c, v, max c v r} J (B s)) :
    (A.scalar h).T.map ((A.scalarTensor k).hom.app (K, L)) ≫
        (A.scalarTensor h).hom.app ((A.scalar k).T.obj K, (A.scalar k).T.obj L) ≫
        (A.levelClosed n).tensor.map
          (Prod.mkHom ((A.scalarComposition h k).hom.app K)
            ((A.scalarComposition h k).hom.app L)) =
      (A.scalarComposition h k).hom.app ((A.levelClosed s).tensor.obj (K, L)) ≫
        (A.scalarTensor (h.trans k)).hom.app (K, L) := by
  have := evaluation_rightAdjoint.{c, v, r} J B τ s
  let E := e.{c, v, max c v r} J B τ s
  let F := E.leftAdjoint
  let adj := Adjunction.ofIsRightAdjoint E
  let P := F.obj K
  let Q := F.obj L
  let p : K ⟶ E.obj P := adj.unit.app K
  let q : L ⟶ E.obj Q := adj.unit.app L
  let R := A.closed.tensor.obj (P, Q)
  let u := (A.levelClosed s).tensor.map (Prod.mkHom p q) ≫
    (A.tensorEvaluation s).inv.app (P, Q)
  let pk := (A.scalar k).T.map p ≫ reduction J B τ k (A.scalar k) P
  let qk := (A.scalar k).T.map q ≫ reduction J B τ k (A.scalar k) Q
  let pn := (A.scalar (h.trans k)).T.map p ≫
    reduction J B τ (h.trans k) (A.scalar (h.trans k)) P
  let qn := (A.scalar (h.trans k)).T.map q ≫
    reduction J B τ (h.trans k) (A.scalar (h.trans k)) Q
  have : IsIso pn := semilinearSingletonEvaluationMate_isIso.{c, v, r} J B τ s n
    (h.trans k) (A.scalar (h.trans k)) F adj K
  have : IsIso qn := semilinearSingletonEvaluationMate_isIso.{c, v, r} J B τ s n
    (h.trans k) (A.scalar (h.trans k)) F adj L
  have hp : (A.scalarComposition h k).hom.app K ≫ pn =
      (A.scalar h).T.map pk ≫ reduction J B τ h (A.scalar h) P := by
    dsimp only [pn, pk]
    have hn := (A.scalarComposition h k).hom.naturality p
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn, ← A.reduction_cocycle h k P]
    simp only [Functor.map_comp, Category.assoc]
  have hq : (A.scalarComposition h k).hom.app L ≫ qn =
      (A.scalar h).T.map qk ≫ reduction J B τ h (A.scalar h) Q := by
    dsimp only [qn, qk]
    have hn := (A.scalarComposition h k).hom.naturality q
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn, ← A.reduction_cocycle h k Q]
    simp only [Functor.map_comp, Category.assoc]
  have wk := tensor_reduction_precompose.{c, v, r} J B τ A k K L P Q p q
  change (A.scalar k).T.map u ≫ reduction J B τ k (A.scalar k) R ≫
      (A.tensorEvaluation m).hom.app (P, Q) =
    (A.scalarTensor k).hom.app (K, L) ≫
      (A.levelClosed m).tensor.map (Prod.mkHom pk qk) at wk
  have wn := tensor_reduction_precompose.{c, v, r} J B τ A (h.trans k) K L P Q p q
  change (A.scalar (h.trans k)).T.map u ≫
      reduction J B τ (h.trans k) (A.scalar (h.trans k)) R ≫
      (A.tensorEvaluation n).hom.app (P, Q) =
    (A.scalarTensor (h.trans k)).hom.app (K, L) ≫
      (A.levelClosed n).tensor.map (Prod.mkHom pn qn) at wn
  have : IsIso (Prod.mkHom pn qn) :=
    (isIso_prod_iff (f := Prod.mkHom pn qn)).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_mono ((A.levelClosed n).tensor.map (Prod.mkHom pn qn))).1
  simp only [Category.assoc]
  rw [← (A.levelClosed n).tensor.map_comp]
  change _ ≫ _ ≫ (A.levelClosed n).tensor.map
    (Prod.mkHom ((A.scalarComposition h k).hom.app K ≫ pn)
      ((A.scalarComposition h k).hom.app L ≫ qn)) = _
  rw [hp, hq]
  have hn := (A.scalarTensor h).hom.naturality (Prod.mkHom pk qk)
  change (A.scalar h).T.map ((A.levelClosed m).tensor.map (Prod.mkHom pk qk)) ≫
      (A.scalarTensor h).hom.app (_, _) =
    (A.scalarTensor h).hom.app (_, _) ≫
      (A.levelClosed n).tensor.map
        (Prod.mkHom ((A.scalar h).T.map pk) ((A.scalar h).T.map qk)) at hn
  rw [← prod_comp
    (Prod.mkHom ((A.scalar h).T.map pk) ((A.scalar h).T.map qk))
    (Prod.mkHom (reduction J B τ h (A.scalar h) P)
      (reduction J B τ h (A.scalar h) Q)), (A.levelClosed n).tensor.map_comp]
  rw [← reassoc_of% hn, ← (A.scalar h).T.map_comp_assoc, ← wk]
  simp only [Functor.map_comp, Category.assoc]
  rw [← tensor_reduction_formula.{c, v, r} J B τ A P Q h,
    reassoc_of% A.reduction_cocycle h k R]
  have hu := (A.scalarComposition h k).hom.naturality u
  dsimp only [Functor.comp_map] at hu
  rw [reassoc_of% hu]
  rw [wn]

end WeilConjectures.SemilinearSections
