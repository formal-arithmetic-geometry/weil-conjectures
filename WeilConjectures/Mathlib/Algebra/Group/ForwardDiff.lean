/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Data.Fintype.Powerset

/-!
# Composites of forward difference operators in different directions

Mathlib's `Mathlib/Algebra/Group/ForwardDiff.lean` studies the iterates `Δ_[h]^[n]` of a *single*
forward difference operator. This file collects the facts one needs about composites
`Δ_[v 0] ∘ ⋯ ∘ Δ_[v (d - 1)]` of difference operators in *different* directions:

* `fwdDiff_comm`: the operators `Δ_[h₁]` and `Δ_[h₂]` commute;
* `fwdDiff_aux.shiftₗ_add`: `h ↦ shiftₗ h` turns addition into multiplication;
* `fwdDiff_add_arg`: `Δ_[h₁ + h₂] f = Δ_[h₁] f + Δ_[h₂] f + Δ_[h₁] (Δ_[h₂] f)`;
* `fwdDiffComp`: the composite `Δ_[v 0] ∘ ⋯ ∘ Δ_[v (d - 1)]` attached to a family
  `v : Fin d → M`, defined as the product of the `fwdDiffₗ (v i)` in the endomorphism ring
  `Module.End ℤ (M → G)`, applied to `f`;
* `fwdDiffComp_eq_sum_powerset`: the expansion of that composite as an alternating sum over the
  subsets of `Fin d`.

These are the operator identities of `lem:deg-difference-explicit` in the blueprint chapter on the
degree of an isogeny.
-/

@[expose] public section

open Finset Function fwdDiff fwdDiff_aux

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] {d : ℕ}

/-- Forward difference operators in different directions commute. -/
lemma fwdDiff_comm (h₁ h₂ : M) (f : M → G) : Δ_[h₁] (Δ_[h₂] f) = Δ_[h₂] (Δ_[h₁] f) := by
  ext y
  simp only [fwdDiff, add_right_comm y h₂ h₁]
  abel

namespace fwdDiff_aux

/-- Forward difference operators in different directions commute. -/
lemma commute_fwdDiffₗ (h₁ h₂ : M) : Commute (fwdDiffₗ M G h₁) (fwdDiffₗ M G h₂) := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply]
  exact fwdDiff_comm h₁ h₂ f

/-- The shift operators compose: `shiftₗ (h₁ + h₂) = shiftₗ h₁ * shiftₗ h₂`. -/
lemma shiftₗ_add (h₁ h₂ : M) : shiftₗ M G (h₁ + h₂) = shiftₗ M G h₁ * shiftₗ M G h₂ := by
  apply LinearMap.ext
  intro f
  funext y
  simp [Module.End.mul_apply, shiftₗ_apply, add_assoc]

/-- The shift operators commute. -/
lemma commute_shiftₗ (h₁ h₂ : M) : Commute (shiftₗ M G h₁) (shiftₗ M G h₂) := by
  rw [Commute, SemiconjBy, ← shiftₗ_add, ← shiftₗ_add, add_comm]

end fwdDiff_aux

/-- The difference operator attached to a sum of directions, in terms of the two summands. -/
lemma fwdDiff_add_arg (h₁ h₂ : M) (f : M → G) :
    Δ_[h₁ + h₂] f = Δ_[h₁] f + Δ_[h₂] f + Δ_[h₁] (Δ_[h₂] f) := by
  ext y
  simp only [fwdDiff, Pi.add_apply, add_assoc]
  abel

/-- The composite `Δ_[v 0] ∘ ⋯ ∘ Δ_[v (d - 1)]` of the forward difference operators attached to a
family of directions `v : Fin d → M`, applied to `f : M → G`.

It is defined as the product of the endomorphisms `fwdDiffₗ (v i)` in `Module.End ℤ (M → G)`,
taken in the order `i = 0, 1, …, d - 1`; by `fwdDiff_comm` the order is immaterial. -/
def fwdDiffComp (v : Fin d → M) (f : M → G) : M → G :=
  (List.ofFn fun i ↦ fwdDiffₗ M G (v i)).prod f

@[simp] lemma fwdDiffComp_zero (v : Fin 0 → M) (f : M → G) : fwdDiffComp v f = f := by
  simp [fwdDiffComp]

lemma fwdDiffComp_succ (v : Fin (d + 1) → M) (f : M → G) :
    fwdDiffComp v f = Δ_[v 0] (fwdDiffComp (fun i ↦ v i.succ) f) := by
  simp only [fwdDiffComp, List.ofFn_succ, List.prod_cons, Module.End.mul_apply, coe_fwdDiffₗ]

/-- The composite of `d + 1` difference operators, with the first operator applied to `f`
first. -/
lemma fwdDiffComp_succ' (v : Fin (d + 1) → M) (f : M → G) :
    fwdDiffComp v f = fwdDiffComp (fun i ↦ v i.succ) (Δ_[v 0] f) := by
  have hc : Commute (fwdDiffₗ M G (v 0))
      (List.ofFn fun i : Fin d ↦ fwdDiffₗ M G (v i.succ)).prod := by
    refine Commute.list_prod_right _ _ fun x hx ↦ ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact commute_fwdDiffₗ _ _
  simp only [fwdDiffComp, List.ofFn_succ, List.prod_cons]
  rw [hc]
  simp only [Module.End.mul_apply, coe_fwdDiffₗ]

/-- Splitting a sum over the subsets of `Fin (d + 1)` according to whether the subset contains
`0` or not. -/
private lemma sum_finsetFinSucc {β : Type*} [AddCommMonoid β] (g : Finset (Fin (d + 1)) → β) :
    ∑ S : Finset (Fin (d + 1)), g S =
      (∑ S : Finset (Fin d), g (S.image Fin.succ)) +
        ∑ S : Finset (Fin d), g (insert 0 (S.image Fin.succ)) := by
  have hinj : ∀ x ∈ (univ : Finset (Finset (Fin d))), ∀ y ∈ (univ : Finset (Finset (Fin d))),
      x.image Fin.succ = y.image Fin.succ → x = y :=
    fun _ _ _ _ h ↦ Finset.image_injective (Fin.succ_injective d) h
  have h0 : (0 : Fin (d + 1)) ∉ (univ : Finset (Fin d)).image Fin.succ := by simp
  have huniv :
      (univ : Finset (Fin (d + 1))) = insert 0 ((univ : Finset (Fin d)).image Fin.succ) := by
    ext i
    refine ⟨fun _ ↦ ?_, fun _ ↦ mem_univ _⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_image_of_mem _ (mem_univ j))
  have hpow : ((univ : Finset (Fin d)).image Fin.succ).powerset =
      (univ : Finset (Finset (Fin d))).image (Finset.image Fin.succ) := by
    rw [Finset.powerset_image, Finset.powerset_univ]
  calc ∑ S : Finset (Fin (d + 1)), g S
      = ∑ S ∈ (univ : Finset (Fin (d + 1))).powerset, g S := by rw [Finset.powerset_univ]
    _ = ∑ S ∈ (insert 0 ((univ : Finset (Fin d)).image Fin.succ)).powerset, g S := by rw [← huniv]
    _ = (∑ S ∈ ((univ : Finset (Fin d)).image Fin.succ).powerset, g S) +
          ∑ S ∈ ((univ : Finset (Fin d)).image Fin.succ).powerset, g (insert 0 S) :=
        Finset.sum_powerset_insert h0 g
    _ = _ := by rw [hpow, Finset.sum_image hinj, Finset.sum_image hinj]

/-- **The composite of `d` forward difference operators as an alternating sum.**

`Δ_[v 0] ⋯ Δ_[v (d - 1)] f` evaluated at `y` is the alternating sum of the values
`f (y + ∑ i ∈ S, v i)` over all subsets `S` of `Fin d`. -/
theorem fwdDiffComp_eq_sum_powerset (v : Fin d → M) (f : M → G) (y : M) :
    fwdDiffComp v f y = ∑ S : Finset (Fin d), (-1 : ℤ) ^ (d - S.card) • f (y + ∑ i ∈ S, v i) := by
  induction d generalizing y with
  | zero =>
    have h : (default : Finset (Fin 0)) = ∅ := Finset.eq_empty_of_isEmpty _
    simp [h]
  | succ d ih =>
    rw [fwdDiffComp_succ]
    simp only [fwdDiff, ih]
    rw [sum_finsetFinSucc (fun S ↦ (-1 : ℤ) ^ (d + 1 - S.card) • f (y + ∑ i ∈ S, v i)),
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    have hcard : S.card ≤ d := le_trans (Finset.card_le_univ S) (by simp)
    have himg : (S.image Fin.succ).card = S.card :=
      Finset.card_image_of_injective S (Fin.succ_injective d)
    have h0 : (0 : Fin (d + 1)) ∉ S.image Fin.succ := by simp [Fin.succ_ne_zero]
    have hsum : ∑ i ∈ S.image Fin.succ, v i = ∑ i ∈ S, v i.succ :=
      Finset.sum_image fun _ _ _ _ h ↦ Fin.succ_injective d h
    have hpow : (-1 : ℤ) ^ (d + 1 - S.card) = -(-1 : ℤ) ^ (d - S.card) := by
      rw [show d + 1 - S.card = (d - S.card) + 1 from by omega, pow_succ]
      ring
    rw [himg, hsum, Finset.card_insert_of_notMem h0, himg, Finset.sum_insert h0, hsum, hpow,
      show d + 1 - (S.card + 1) = d - S.card from by omega, ← add_assoc]
    simp only [neg_smul]
    abel
