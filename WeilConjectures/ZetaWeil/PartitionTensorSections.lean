/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
import WeilConjectures.CategoryTheory.Sites.IsDisjointCover.DisjointSheafSections
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Tensor sections over finite disjoint partitions

Source: Stacks Project, Tags 03EK and 0F63.
(blueprint: lem-zl-partition-tensor-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

section Partition
variable {W : C} {n : ℕ} {Y : Fin n → C} {f : ∀ i, Y i ⟶ W}
  (hf : J.IsDisjointCover f)

private abbrev rings :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

private abbrev Mods := SheafOfModules.{max c v r} (rings.{c, v, r} R)

private abbrev underlying (M : Mods.{c, v, r} R) : Sheaf J (Type (max c v r)) :=
  (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max c v r})).obj
    ((toSheaf (rings.{c, v, r} R)).obj M)

private def extend (M : Mods.{c, v, r} R) (i : Fin n) (x : M.val.obj (op (Y i))) :
    M.val.obj (op W) := by
  classical
  exact (GrothendieckTopology.IsDisjointCover.exists_type_map_eq hf (underlying.{c, v, r} R M)
    (Pi.single (M := fun j ↦ M.val.obj (op (Y j))) i x)).choose

private theorem restrict_extend (M : Mods.{c, v, r} R) (i : Fin n)
    (x : M.val.obj (op (Y i))) (j : Fin n) :
    M.val.restrictₛₗ (f j).op (extend.{c, v, r} R hf M i x) = Pi.single (M := fun j ↦ M.val.obj (op
      (Y j))) i x j := by
  classical
  exact (GrothendieckTopology.IsDisjointCover.exists_type_map_eq hf (underlying.{c, v, r} R M)
    (Pi.single (M := fun j ↦ M.val.obj (op (Y j))) i x)).choose_spec j

private theorem extend_zero (M : Mods.{c, v, r} R) (i : Fin n) : extend.{c, v, r} R hf M i 0 = 0 :=
  by
  classical
  apply GrothendieckTopology.IsDisjointCover.type_ext hf (underlying.{c, v, r} R M)
  intro j
  change M.val.restrictₛₗ (f j).op _ = M.val.restrictₛₗ (f j).op _
  simp only [restrict_extend.{c, v, r}, map_zero, Pi.single_zero, Pi.zero_apply]

private theorem extend_add (M : Mods.{c, v, r} R) (i : Fin n)
    (x y : M.val.obj (op (Y i))) :
    extend.{c, v, r} R hf M i (x + y) = extend.{c, v, r} R hf M i x + extend.{c, v, r} R hf M i y :=
      by
  classical
  apply GrothendieckTopology.IsDisjointCover.type_ext hf (underlying.{c, v, r} R M)
  intro j
  change M.val.restrictₛₗ (f j).op _ = M.val.restrictₛₗ (f j).op _
  simp only [restrict_extend.{c, v, r}, map_add, Pi.single_add, Pi.add_apply]

private abbrev underlyingRing : Sheaf J (Type (max c v r)) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).obj R

private def extendScalar (i : Fin n) (a : R.obj.obj (op (Y i))) :
    R.obj.obj (op W) := by
  classical
  exact (GrothendieckTopology.IsDisjointCover.exists_type_map_eq hf
    (underlyingRing.{c, v, r} R)
      (Pi.single (M := fun j ↦ R.obj.obj (op (Y j))) i a)).choose

private theorem restrict_extendScalar (i j : Fin n) (a : R.obj.obj (op (Y i))) :
    R.obj.map (f j).op (extendScalar.{c, v, r} R hf i a) =
      Pi.single (M := fun j ↦ R.obj.obj (op (Y j))) i a j := by
  classical
  exact (GrothendieckTopology.IsDisjointCover.exists_type_map_eq hf
    (underlyingRing.{c, v, r} R)
      (Pi.single (M := fun j ↦ R.obj.obj (op (Y j))) i a)).choose_spec j

private theorem restrict_smul (M : Mods.{c, v, r} R) {V V' : Cᵒᵖ}
    (g : V ⟶ V') (a : R.obj.obj V) (x : M.val.obj V) :
    M.val.restrictₛₗ g (a • x) = R.obj.map g a • M.val.restrictₛₗ g x :=
  M.val.map_smul g a x

private theorem tensor_restrict_tmul (M N : Mods.{c, v, r} R) {V V' : Cᵒᵖ}
    (g : V ⟶ V') (x : M.val.obj V) (y : N.val.obj V) :
    (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val).restrictₛₗ g (x ⊗ₜ[R.obj.obj V]
      y) =
      M.val.restrictₛₗ g x ⊗ₜ[R.obj.obj V'] N.val.restrictₛₗ g y := rfl

private theorem extend_smul (M : Mods.{c, v, r} R) (i : Fin n)
    (a : R.obj.obj (op (Y i))) (x : M.val.obj (op (Y i))) :
    extend.{c, v, r} R hf M i (a • x) = extendScalar.{c, v, r} R hf i a • extend.{c, v, r} R hf M i
      x := by
  classical
  apply GrothendieckTopology.IsDisjointCover.type_ext hf (underlying.{c, v, r} R M)
  intro j
  change M.val.restrictₛₗ (f j).op _ = M.val.restrictₛₗ (f j).op _
  rw [restrict_extend.{c, v, r}, restrict_smul.{c, v, r},
    restrict_extendScalar.{c, v, r}, restrict_extend.{c, v, r}]
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

private def extendTensor (M N : Mods.{c, v, r} R) (i : Fin n) :
    M.val.obj (op (Y i)) ⊗[R.obj.obj (op (Y i))] N.val.obj (op (Y i)) →+
      M.val.obj (op W) ⊗[R.obj.obj (op W)] N.val.obj (op W) :=
  TensorProduct.liftAddHom
    { toFun := fun x ↦
        { toFun := fun y ↦ extend.{c, v, r} R hf M i x ⊗ₜ extend.{c, v, r} R hf N i y
          map_zero' := by rw [extend_zero.{c, v, r}, TensorProduct.tmul_zero]
          map_add' := by intros; rw [extend_add.{c, v, r}, TensorProduct.tmul_add] }
      map_zero' := by ext y; dsimp; rw [extend_zero.{c, v, r}, TensorProduct.zero_tmul]
      map_add' := by intros; ext y; dsimp; rw [extend_add.{c, v, r}, TensorProduct.add_tmul] }
    (by intro a x y; dsimp; rw [extend_smul.{c, v, r}, extend_smul.{c, v, r},
      TensorProduct.smul_tmul])

private theorem restrict_extendTensor (M N : Mods.{c, v, r} R) (i j : Fin n)
    (t : (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val).obj (op (Y i))) :
    (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val).restrictₛₗ (f j).op
      (extendTensor.{c, v, r} R hf M N i t) = Pi.single (M := fun j ↦
      (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val).obj (op (Y j))) i t j := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul x y =>
    change (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val).restrictₛₗ (f j).op
      (extend.{c, v, r} R hf M i x ⊗ₜ extend.{c, v, r} R hf N i y) = _
    erw [tensor_restrict_tmul.{c, v, r} R M N (f j).op,
      restrict_extend.{c, v, r}, restrict_extend.{c, v, r}]
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  | add x y hx hy => simp only [map_add, hx, hy, Pi.single_add, Pi.add_apply]

private def partitionScalar (i : Fin n) : R.obj.obj (op W) :=
  extendScalar.{c, v, r} R hf i 1

private theorem restrict_partitionScalar (i j : Fin n) :
    R.obj.map (f j).op (partitionScalar.{c, v, r} R hf i) = Pi.single (M := fun j ↦ R.obj.obj (op (Y
      j))) i 1 j :=
  restrict_extendScalar.{c, v, r} R hf i j 1

private theorem extend_restrict (M : Mods.{c, v, r} R) (i : Fin n) (x : M.val.obj (op W)) :
    extend.{c, v, r} R hf M i (M.val.restrictₛₗ (f i).op x) = partitionScalar.{c, v, r} R hf i • x
      := by
  classical
  apply GrothendieckTopology.IsDisjointCover.type_ext hf (underlying.{c, v, r} R M)
  intro j
  change M.val.restrictₛₗ (f j).op _ = M.val.restrictₛₗ (f j).op _
  rw [restrict_extend.{c, v, r}, restrict_smul.{c, v, r},
    restrict_partitionScalar.{c, v, r}]
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

private theorem partitionScalar_idem (i : Fin n) :
    partitionScalar.{c, v, r} R hf i * partitionScalar.{c, v, r} R hf i = partitionScalar.{c, v, r}
      R hf i := by
  classical
  apply GrothendieckTopology.IsDisjointCover.type_ext hf (underlyingRing.{c, v, r} R)
  intro j
  change R.obj.map (f j).op (_ * _) = R.obj.map (f j).op _
  simp only [map_mul, restrict_partitionScalar.{c, v, r}]
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

private theorem sum_partitionScalar : ∑ i, partitionScalar.{c, v, r} R hf i = 1 := by
  classical
  apply GrothendieckTopology.IsDisjointCover.type_ext hf (underlyingRing.{c, v, r} R)
  intro j
  change R.obj.map (f j).op (∑ i, _) = R.obj.map (f j).op 1
  simp only [map_sum, restrict_partitionScalar.{c, v, r}, map_one]
  simp

private theorem tensor_partition_identity (M N : Mods.{c, v, r} R)
    (t : (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val).obj (op W)) :
    ∑ i, extendTensor.{c, v, r} R hf M N i ((PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val
      N.val).restrictₛₗ (f i).op t) = t := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    trans (∑ i, extend.{c, v, r} R hf M i (M.val.restrictₛₗ (f i).op x) ⊗ₜ
      extend.{c, v, r} R hf N i (N.val.restrictₛₗ (f i).op y))
    · apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (extendTensor.{c, v, r} R hf M N i)
        (tensor_restrict_tmul.{c, v, r} R M N (f i).op x y)
    · trans ∑ i, partitionScalar.{c, v, r} R hf i •
        (x ⊗ₜ[R.obj.obj (op W)] y)
      · apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = (partitionScalar.{c, v, r} R hf i • x) ⊗ₜ[R.obj.obj (op W)]
              (partitionScalar.{c, v, r} R hf i • y) :=
            congrArg₂ (fun (a : M.val.obj (op W)) (b : N.val.obj (op W)) ↦
              a ⊗ₜ[R.obj.obj (op W)] b)
                (extend_restrict.{c, v, r} R hf M i x)
                (extend_restrict.{c, v, r} R hf N i y)
          _ = _ :=
            (TensorProduct.smul_tmul_smul (partitionScalar.{c, v, r} R hf i)
              (partitionScalar.{c, v, r} R hf i) x y).trans
                (congrArg (fun a : R.obj.obj (op W) ↦ a •
                  (x ⊗ₜ[R.obj.obj (op W)] y)) (partitionScalar_idem.{c, v, r} R hf i))
      · rw [← Finset.sum_smul, sum_partitionScalar.{c, v, r}, one_smul]
        rfl
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]

/-- Raw tensor sections satisfy descent for a finite disjoint cover, including
variable coefficient rings on the pieces.

Source: Stacks Project, Tags 03EK and 0F63
(blueprint: lem-zl-partition-tensor-sections).

Proof: extend sections on a piece by zero on every other piece and glue. This
extension is additive and respects multiplication by a scalar extended by zero.
Consequently the tensor of two extensions is balanced over the piece's ring,
and descends to an additive map on its tensor product. Summing these maps is an
inverse to restriction. For the other composite, the extensions of the local
units are orthogonal idempotents summing to one, so the identity holds on pure
tensors, hence on all tensors by additivity. -/
theorem tensorSections_bijective_of_disjointCover
    (M N : SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    Function.Bijective (fun t : (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val).obj
      (op W) ↦
      fun i ↦ (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val).restrictₛₗ (f i).op t)
        := by
  classical
  constructor
  · intro x y h
    rw [← tensor_partition_identity.{c, v, r} R hf M N x, ← tensor_partition_identity.{c, v, r} R hf
      M N y]
    exact Finset.sum_congr rfl (fun i _ ↦ congrArg (extendTensor.{c, v, r} R hf M N i) (congrFun h
      i))
  · intro t
    refine ⟨∑ i, extendTensor.{c, v, r} R hf M N i (t i), ?_⟩
    funext j
    simp only [map_sum, restrict_extendTensor.{c, v, r}]
    simp

include hf in
end Partition
end SheafOfModules
