/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinateData
import Sheaf.CategoryTheory.BarHomogeneousInclusion
import Sheaf.CategoryTheory.InternalBarZeroEvaluation
import Sheaf.CategoryTheory.InternalBarRestrictionEvaluation
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Internal homogeneous cochain coordinates

The bar complex itself presents the homogeneous submodule via the successive-quotient
inclusion. Coordinate change is therefore the identity on this presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

private theorem coordinateQuotients_prefixes {J : ProfiniteGrp.{u}}
    {T : Profinite.{u}} {n : ℕ} (g : Fin n → C(T, J)) :
    coordinateQuotients (coordinatePrefixes g) = g := by
  funext i
  dsimp [coordinateQuotients, coordinatePrefixes]
  rw [List.prod_take_succ _ i.val (by simp)]
  simp

private theorem coordinatePrefixes_zero {J : ProfiniteGrp.{u}}
    {T : Profinite.{u}} {n : ℕ} (g : Fin n → C(T, J)) :
    coordinatePrefixes g 0 = 1 := by
  simp [coordinatePrefixes]

private theorem coordinateQuotients_comp {K J : ProfiniteGrp.{u}}
    (v : K →ₜ* J) {T : Profinite.{u}} {n : ℕ} (x : Fin (n + 1) → C(T, K)) :
    coordinateQuotients (fun i ↦ v.toContinuousMap.comp (x i)) =
      fun i ↦ v.toContinuousMap.comp (coordinateQuotients x i) := by
  funext i
  ext t
  simp [coordinateQuotients]

/-- Internal homogeneous and inhomogeneous bar cochains have the specified natural inverse
coordinate maps and the induced isomorphism in the ordinary derived category, for every
given internal function presentation `F` and every given family of bar diagrams `bar`
specified by def-sfb-condensed-equivariant-bar-data (not merely for some chosen model).

Source: Stacks Project, Tag 0DVG, displayed bar differential; the internal sheaf adaptation
is the DAG calculation (blueprint: lem-sfb-internal-homogeneous-cochain-coordinates).

Proof: use the free/internal-Hom adjunction of def-sfb-condensed-equivariant-bar-data to
construct the evaluation-family models. On the whole slice over S, define Phi by prefix
products and Psi by successive quotients followed by the x₀-action. Products and inverses
are continuous, both operations commute with restriction, and action is linear. Psi is
homogeneous because (a x)⁻¹(a y) = x⁻¹y and the action is associative. Prefix products
and successive quotients cancel; the other composite is the identity by homogeneity.
Deletion preserves homogeneity. In its square, the deletions of i then j−1 and of j then i
have opposite signs, so cancel, including in characteristic two. Evaluating deletion on
prefixes gives the action face when the initial entry is deleted, multiplication faces
in the interior, and the last face at the end: exactly the bar differential of 0DVG.
Thus Phi commutes with differentials; its inverse Psi does too. At n = 0 the formulas
are F ↦ F(1) and m ↦ (x ↦ xm). Equivariant coefficient maps commute with evaluation and
action, giving coefficient naturality. Restriction along v commutes with prefix products
and quotients and uses the inflated action, giving both restriction squares. Extend by
zero in negative degrees and apply Q to the inverse maps to obtain the displayed derived
isomorphism. No injectivity, trivial action, rationality or topological presentation is used.
-/
theorem exists_internalHomogeneousCochainCoordinates (A : Ring.{u})
    (F : InternalFunctions A) (bar : ∀ J : ProfiniteGrp.{u}, BarDiagram (G := J) F) :
    Nonempty (InternalCochainCoordinates A F bar) := by
  let I : ∀ J : ProfiniteGrp.{u}, BarHomogeneousInclusion F J (bar J) :=
    fun J ↦ Classical.choice (exists_barHomogeneousInclusion F J (bar J))
  let H : ∀ J : ProfiniteGrp.{u}, InternalHomogeneousCochains F J := fun J ↦
    { complex := cochains (bar J)
      inclusion := (I J).inclusion
      injective := (I J).injective
      image := (I J).image
      maps := (I J).maps
      differential := (I J).differential }
  let Z := fun (J : ProfiniteGrp.{u}) (M : Equivariant A J) ↦
    Classical.choose (exists_internalBarZeroEvaluation F J (bar J) M)
  have hZ := fun (J : ProfiniteGrp.{u}) (M : Equivariant A J) ↦
    Classical.choose_spec (exists_internalBarZeroEvaluation F J (bar J) M)
  let R := fun (K J : ProfiniteGrp.{u}) (v : K →ₜ* J) ↦
    Classical.choose (exists_internalBarRestrictionEvaluation F K J v (bar J) (bar K))
  have hR := fun (K J : ProfiniteGrp.{u}) (v : K →ₜ* J) ↦
    Classical.choose_spec
      (exists_internalBarRestrictionEvaluation F K J v (bar J) (bar K))
  refine ⟨{
    homogeneous := H
    coordinates := fun J ↦ Iso.refl (cochains (bar J))
    phi := ?_
    psi := ?_
    zero := Z
    zero_eval := hZ
    phi_zero := ?_
    psi_zero := ?_
    homogeneousRestriction := R
    inhomogeneousRestriction := R
    homogeneousRestriction_eval := ?_
    inhomogeneousRestriction_eval := hR
    restriction_phi := ?_
    restriction_psi := ?_
    derived := ?_ }⟩
  · intro J M n S x T f g
    change inhomogeneousCoordinateValue (bar J) M n S x T f g =
      (F.evaluate (power J (n + 1)) S M.module
        (((I J).inclusion M n).hom.hom.app (op S) x)).val T f
          (tupleMap (coordinatePrefixes g))
    rw [(I J).evaluation, coordinateQuotients_prefixes, coordinatePrefixes_zero]
    simp
  · intro J M n S c T f x
    exact (I J).evaluation M n S c T f x
  · intro J M S x
    change (Z J M).hom.hom.hom.app (op S) x =
      (F.evaluate (power J 1) S M.module
        (((I J).inclusion M 0).hom.hom.app (op S) x)).val S (𝟙 S)
          (tupleMap (fun _ ↦ 1))
    rw [(I J).evaluation]
    rw [hZ J M S x S (𝟙 S) (coordinateQuotients (fun _ ↦ 1))]
    simp [Z]
  · intro J M S m T f g
    change (F.evaluate (power J 1) S M.module
      (((I J).inclusion M 0).hom.hom.app (op S)
        ((Z J M).inv.hom.hom.app (op S) m))).val T f (tupleMap (fun _ ↦ g)) = _
    rw [(I J).evaluation]
    rw [hZ J M S ((Z J M).inv.hom.hom.app (op S) m) T f
      (coordinateQuotients (fun _ ↦ g))]
    have hz : (Z J M).hom.hom.hom.app (op S)
        ((Z J M).inv.hom.hom.app (op S) m) = m := by
      have h := congrArg (fun k ↦ k.hom.hom.app (op S) m) (Z J M).inv_hom_id
      exact h
    rw [hz]
  · intro K J v M n S x T f g
    change (F.evaluate (power K (n + 1)) S
      ((Profinite.CondensedAction.inflate v).obj M).module
      (((I K).inclusion ((Profinite.CondensedAction.inflate v).obj M) n).hom.hom.app
        (op S) ((((R K J v).app M).f n).hom.hom.app (op S) x))).val T f (tupleMap g) =
      (F.evaluate (power J (n + 1)) S M.module
        (((I J).inclusion M n).hom.hom.app (op S) x)).val T f
          (tupleMap (fun i ↦ v.toContinuousMap.comp (g i)))
    rw [(I K).evaluation, (I J).evaluation,
      hR K J v M n S x T f (coordinateQuotients g), coordinateQuotients_comp]
    rfl
  · intro K J v M
    change (R K J v).app M ≫ 𝟙 _ = 𝟙 _ ≫ (R K J v).app M
    simp only [Category.comp_id, Category.id_comp]
  · intro K J v M
    change (R K J v).app M ≫ 𝟙 _ = 𝟙 _ ≫ (R K J v).app M
    simp only [Category.comp_id, Category.id_comp]
  · intro J M
    refine ⟨Iso.refl _, ?_, ?_⟩
    all_goals
      change 𝟙 ((coordinateLocalization A).obj (extend ((cochains (bar J)).obj M))) =
        (coordinateLocalization A).map
          (HomologicalComplex.extendMap (𝟙 ((cochains (bar J)).obj M))
            ComplexShape.embeddingUpNat)
      rw [HomologicalComplex.extendMap_id, Functor.map_id]

end CategoryTheory.CondensedBar
