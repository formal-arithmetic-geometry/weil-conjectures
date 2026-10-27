/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtension

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Orthogonality of a nearest-point residual

Source: Weil conjectures blueprint, main-20261015,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
auxiliary nearest-point residual calculation
(blueprint: lem-sfb-ultrametric-orthogonal-extension).
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

universe u v

namespace Padic

/-- A nearest-point residual extends a finite orthogonal family over a finite
extension of `ℚ_[ℓ]`.

Source: Weil conjectures blueprint, main-20261015,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
auxiliary nearest-point residual calculation
(blueprint: lem-sfb-ultrametric-orthogonal-extension).

Proof: Let `b = x - w`. Definiteness and `x ∉ W` give `b ≠ 0` and positive
norm. Minimality gives `‖b‖ ≤ ‖x-z‖` for every `z ∈ W`. For `u ∈ W` and
`a ∈ E`, this yields the lower bound `‖u + a b‖ ≥ |a|_E ‖b‖`; applying the
ultrametric inequality to `u = (u + a b) - a b` gives the other lower bound,
so `‖u + a b‖ = max (‖u‖, |a|_E ‖b‖)`. Substitution of the old orthogonality
formula proves the enlarged formula, including `n = 0`. The formula and
`b ≠ 0` give linear independence, and `b = x - w` gives the asserted span.
-/
theorem ultrametric_orthogonal_extension
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (V : Type v) [AddCommGroup V] [Module E V]
    (norm : V → NNReal)
    (hscale : ∀ (a : E) (z : V),
      norm (a • z) = Real.toNNReal (coefficientExtensionAbsoluteValue l E a) * norm z)
    (htriangle : ∀ (z₁ z₂ : V),
      norm (z₁ + z₂) ≤ max (norm z₁) (norm z₂))
    (hdefinite : ∀ z : V, norm z = 0 ↔ z = 0)
    (n : ℕ) (b : Fin n → V) (hlin : LinearIndependent E b)
    (horth : ∀ (a : Fin n → E),
      norm (∑ i, a i • b i) =
        Finset.univ.sup (fun i =>
          Real.toNNReal (coefficientExtensionAbsoluteValue l E (a i)) * norm (b i)))
    (x : V) (hx : x ∉ (Submodule.span E (Set.range b) : Set V))
    (w : V) (hw : w ∈ Submodule.span E (Set.range b))
    (hmin : norm (x - w) =
      sInf (Set.image (fun z : V => norm (x - z))
        (Submodule.span E (Set.range b) : Set V))) :
    x - w ≠ 0 ∧
      (∀ (a : Fin (n + 1) → E),
        norm (∑ i, a i • Fin.snoc (α := fun _ => V) b (x - w) i) =
          Finset.univ.sup (fun i =>
            Real.toNNReal (coefficientExtensionAbsoluteValue l E (a i)) *
              norm (Fin.snoc (α := fun _ => V) b (x - w) i))) ∧
      LinearIndependent E (Fin.snoc (α := fun _ => V) b (x - w)) ∧
      Submodule.span E (Set.range (Fin.snoc (α := fun _ => V) b (x - w))) =
        Submodule.span E (Set.range b) + Submodule.span E ({x} : Set V) := by
  classical
  let W := Submodule.span E (Set.range b)
  have hw' : w ∈ W := hw
  have hx' : x ∉ W := hx
  have hres : x - w ∉ W := by
    intro h
    exact hx' (by simpa using W.add_mem h hw')
  have hne : x - w ≠ 0 := by
    apply (hdefinite _).not.mp
    intro h
    exact hres ((hdefinite _).mp h ▸ W.zero_mem)
  have hneg (z : V) : norm (-z) = norm z := by
    simpa using hscale (-1) z
  have hminimal (z : V) (hz : z ∈ W) : norm (x - w) ≤ norm (x - z) := by
    rw [hmin]
    exact csInf_le (OrderBot.bddBelow _) ⟨z, hz, rfl⟩
  have hlower (u : V) (hu : u ∈ W) (a : E) :
      Real.toNNReal (coefficientExtensionAbsoluteValue l E a) * norm (x - w) ≤
        norm (u + a • (x - w)) := by
    by_cases ha : a = 0
    · subst a
      simp
    · have hid : u + a • (x - w) = a • (x - (w - a⁻¹ • u)) := by
        simp [smul_sub, smul_smul, ha]
        abel
      rw [hid, hscale]
      exact mul_le_mul_of_nonneg_left (hminimal _ (W.sub_mem hw' (W.smul_mem _ hu))) (by positivity)
  have htwo (u : V) (hu : u ∈ W) (a : E) :
      norm (u + a • (x - w)) =
        max (norm u)
          (Real.toNNReal (coefficientExtensionAbsoluteValue l E a) * norm (x - w)) := by
    apply le_antisymm
    · simpa only [hscale] using htriangle u (a • (x - w))
    · apply max_le _ (hlower u hu a)
      have ht := htriangle (u + a • (x - w)) (-(a • (x - w)))
      simp only [add_neg_cancel_right, hneg, hscale] at ht
      exact ht.trans (max_le le_rfl (hlower u hu a))
  refine ⟨hne, ?_, hlin.finSnoc hres, ?_⟩
  · intro a
    have hu : (∑ i : Fin n, a i.castSucc • b i) ∈ W := by
      exact W.sum_mem fun i _ ↦ W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [htwo _ hu, horth]
    apply le_antisymm
    · apply max_le
      · apply Finset.sup_le
        intro i _
        simpa only [Fin.snoc_castSucc] using
          (Finset.le_sup (f := fun j : Fin (n + 1) ↦
            Real.toNNReal (coefficientExtensionAbsoluteValue l E (a j)) *
              norm (Fin.snoc (α := fun _ ↦ V) b (x - w) j)) (Finset.mem_univ i.castSucc))
      · simpa only [Fin.snoc_last] using
          (Finset.le_sup (f := fun j : Fin (n + 1) ↦
            Real.toNNReal (coefficientExtensionAbsoluteValue l E (a j)) *
              norm (Fin.snoc (α := fun _ ↦ V) b (x - w) j)) (Finset.mem_univ (Fin.last n)))
    · apply Finset.sup_le
      intro i _
      cases i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact le_max_right _ _
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact le_trans
          (Finset.le_sup (f := fun j : Fin n ↦
            Real.toNNReal (coefficientExtensionAbsoluteValue l E (a j.castSucc)) *
              norm (b j)) (Finset.mem_univ i)) (le_max_left _ _)
  · rw [Fin.range_snoc, Submodule.span_insert, Submodule.add_eq_sup]
    apply le_antisymm
    · apply sup_le
      · apply (Submodule.span_singleton_le_iff_mem _ _).2
        exact (W ⊔ Submodule.span E {x}).sub_mem
          (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x)))
          (Submodule.mem_sup_left hw')
      · exact le_sup_left
    · apply sup_le
      · exact le_sup_right
      · apply (Submodule.span_singleton_le_iff_mem _ _).2
        have hb : x - w ∈ Submodule.span E {x - w} ⊔ W :=
          Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
        simpa using (Submodule.span E {x - w} ⊔ W).add_mem hb (Submodule.mem_sup_right hw')

end Padic
