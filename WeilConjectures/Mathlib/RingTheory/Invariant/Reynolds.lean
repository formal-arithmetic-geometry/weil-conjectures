/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Algebra.Basic

/-!
# Invariants of a finite group of invertible order and base change

Let `G` be a finite group acting on an `A`-algebra `C` by `A`-algebra automorphisms, with
`A = C^G` and `|G|` invertible in `A`. Averaging over `G` (the Reynolds operator) shows that
taking invariants commutes with reduction modulo an ideal `J ⊆ A`:

* `Algebra.IsInvariant.exists_sub_algebraMap_mem_map`: an element of `C` which is invariant
  modulo `J C` is congruent modulo `J C` to an element of `A`;
* `Algebra.IsInvariant.mem_of_algebraMap_mem_map`: `A ∩ J C = J`.
-/

@[expose] public section

open Finset

namespace Algebra.IsInvariant

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] {G : Type*} [Group G] [Fintype G]
  [MulSemiringAction G C] [Algebra.IsInvariant A C G]

variable (G) in
/-- The sum over a `G`-orbit is invariant, hence comes from `A`. -/
lemma exists_algebraMap_eq_sum_smul (c : C) : ∃ a : A, algebraMap A C a = ∑ g : G, g • c := by
  refine Algebra.IsInvariant.isInvariant (A := A) (G := G) _ fun h ↦ ?_
  rw [smul_sum]
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun _ ↦ rfl

/-- If `|G|` is invertible, an element of `C` which is `G`-invariant modulo `J C` is congruent
modulo `J C` to an element of `A`. -/
lemma exists_sub_algebraMap_mem_map (hG : IsUnit (Fintype.card G : A)) (J : Ideal A) {c : C}
    (hc : ∀ g : G, g • c - c ∈ J.map (algebraMap A C)) :
    ∃ a : A, c - algebraMap A C a ∈ J.map (algebraMap A C) := by
  obtain ⟨a₀, ha₀⟩ := exists_algebraMap_eq_sum_smul (A := A) G c
  refine ⟨↑hG.unit⁻¹ * a₀, ?_⟩
  have h1 : algebraMap A C ↑hG.unit⁻¹ * (Fintype.card G : C) = 1 := by
    rw [← map_natCast (algebraMap A C), ← map_mul, IsUnit.val_inv_mul, map_one]
  have : c - algebraMap A C (↑hG.unit⁻¹ * a₀) =
      algebraMap A C ↑hG.unit⁻¹ * ∑ g : G, -(g • c - c) := by
    rw [map_mul, ha₀]
    simp only [neg_sub, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_sub, ← mul_assoc,
      h1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Submodule.sum_mem _ fun g _ ↦ (Ideal.neg_mem_iff _).2 (hc g))

/-- If `|G|` is invertible and `A → C` is injective, then `A ∩ J C = J`. -/
lemma mem_of_algebraMap_mem_map [SMulCommClass G A C] (hG : IsUnit (Fintype.card G : A))
    (hinj : Function.Injective (algebraMap A C)) (J : Ideal A) {a : A}
    (ha : algebraMap A C a ∈ J.map (algebraMap A C)) : a ∈ J := by
  have key (x : C) (hx : x ∈ J • (⊤ : Submodule A C)) :
      ∃ b ∈ J, algebraMap A C b = ∑ g : G, g • x := by
    induction hx using Submodule.smul_induction_on' with
    | smul r hr n _ =>
      obtain ⟨b, hb⟩ := exists_algebraMap_eq_sum_smul (A := A) G n
      refine ⟨r * b, J.mul_mem_right _ hr, ?_⟩
      simp_rw [smul_comm _ r n, ← smul_sum, ← hb, Algebra.smul_def, map_mul]
    | add x _ y _ hx hy =>
      obtain ⟨b, hb, hbx⟩ := hx
      obtain ⟨b', hb', hby⟩ := hy
      exact ⟨b + b', J.add_mem hb hb', by simp [hbx, hby, sum_add_distrib]⟩
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at ha
  obtain ⟨b, hb, hab⟩ := key _ ha
  simp_rw [smul_algebraMap, sum_const, card_univ, nsmul_eq_mul, ← map_natCast (algebraMap A C),
    ← map_mul] at hab
  rw [← one_mul a, ← IsUnit.val_inv_mul hG, mul_assoc, ← hinj hab]
  exact J.mul_mem_left _ hb

end Algebra.IsInvariant
