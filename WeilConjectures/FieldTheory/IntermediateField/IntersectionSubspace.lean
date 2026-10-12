/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Subspaces meeting `K_α ^ n` for a directed family of subfields

Let `K / k` be a field extension and `(K_α)` a nonempty directed family of intermediate fields
with intersection `k`. A `K`-subspace `V ⊆ K ^ n` contains a nonzero vector with coordinates in
`k` if and only if it contains, for every `α`, a nonzero vector with coordinates in `K_α`
(Stacks, Lemma 07P3).

## References

- Stacks Project, Lemma 15.47.2, <https://stacks.math.columbia.edu/tag/07P3>
-/

@[expose] public section

/-- **A subspace meeting every `K_α ^ n` meets `k ^ n`.** Let `K / k` be a field extension and
`(K_α)_{α ∈ A}` a nonempty family of intermediate fields (so `k ⊆ K_α`) with `⋂ K_α = k` and
such that any two `K_α, K_α'` contain a third `K_α''`. Then for every `n` and every `K`-subspace
`V ⊆ K ^ n`, `V` contains a nonzero vector with all coordinates in `k` if and only if it
contains, for every `α`, a nonzero vector with all coordinates in `K_α`.

(blueprint: `lem-weil-pbc-intersection-subfields-subspace`) -/
theorem IntermediateField.exists_ne_zero_mem_base_iff_forall_mem_intermediateField
    {k K : Type*} [Field k] [Field K] [Algebra k K] {A : Type*} [Nonempty A]
    (Kα : A → IntermediateField k K) (hinf : ⨅ α, Kα α = ⊥)
    (hdir : ∀ α α', ∃ α'', Kα α'' ≤ Kα α ⊓ Kα α') (n : ℕ) (V : Submodule K (Fin n → K)) :
    (∃ v ∈ V, v ≠ 0 ∧ ∀ i, v i ∈ Set.range (algebraMap k K)) ↔
      ∀ α, ∃ v ∈ V, v ≠ 0 ∧ ∀ i, v i ∈ Kα α := by
  constructor
  · rintro ⟨v, hv, hv0, hk⟩ α
    refine ⟨v, hv, hv0, fun i => ?_⟩
    obtain ⟨c, hc⟩ := hk i
    rw [← hc]; exact (Kα α).algebraMap_mem c
  induction n with
  | zero =>
    intro h
    obtain ⟨v, -, hv0, -⟩ := h (Classical.arbitrary A)
    exact absurd (funext fun i => i.elim0) hv0
  | succ n ih =>
    intro h
    let ι : (Fin n → K) →ₗ[K] (Fin (n + 1) → K) :=
      LinearMap.pi fun j => Fin.cases (0 : (Fin n → K) →ₗ[K] K) (fun i => LinearMap.proj i) j
    have hι0 : ∀ x, ι x 0 = 0 := fun x => by simp [ι]
    have hιs : ∀ x (i : Fin n), ι x i.succ = x i := fun x i => by simp [ι]
    have hιinj : ∀ x, ι x = 0 → x = 0 := fun x hx => funext fun i => by
      rw [← hιs x i, hx]; rfl
    let W := V.comap ι
    by_cases hW : ∃ w ∈ W, w ≠ 0 ∧ ∀ i, w i ∈ Set.range (algebraMap k K)
    · obtain ⟨w, hwW, hw0, hwk⟩ := hW
      refine ⟨ι w, hwW, fun h => hw0 (hιinj w h), fun j => ?_⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [hι0]; exact ⟨0, map_zero _⟩
      · rw [hιs]; exact hwk i
    obtain ⟨α, hα⟩ : ∃ α, ∀ w ∈ W, w ≠ 0 → ¬ ∀ i, w i ∈ Kα α := by
      by_contra hc
      push Not at hc
      exact hW (ih W fun α => by
        obtain ⟨w, hw, hw0, hwα⟩ := hc α
        exact ⟨w, hw, hw0, hwα⟩)
    -- vectors of `V` with first coordinate `0` and coordinates in `Kα α` vanish
    have hzero : ∀ z ∈ V, z 0 = 0 → (∀ i, z i ∈ Kα α) → z = 0 := by
      intro z hz hz0 hzα
      have hzι : z = ι (Fin.tail z) := funext fun j => by
        refine Fin.cases ?_ (fun i => ?_) j
        · rw [hι0, hz0]
        · rw [hιs]; rfl
      by_contra hne
      refine hα (Fin.tail z) (by rw [Submodule.mem_comap, ← hzι]; exact hz)
        (fun h => hne (by rw [hzι, h, map_zero])) (fun i => hzα i.succ)
    obtain ⟨w, hwV, hw0, hwα⟩ := h α
    have hw1 : w 0 ≠ 0 := fun h => hw0 (hzero w hwV h hwα)
    set v := (w 0)⁻¹ • w with hv
    have hvV : v ∈ V := V.smul_mem _ hwV
    have hv0 : v 0 = 1 := by simp [hv, hw1]
    have hvα : ∀ i, v i ∈ Kα α := fun i => by
      simp only [hv, Pi.smul_apply, smul_eq_mul]
      exact mul_mem (inv_mem (hwα 0)) (hwα i)
    -- every vector of `V` with coordinates in some `Kα β ≤ Kα α` is a multiple of `v`
    have hmult : ∀ β, Kα β ≤ Kα α → ∀ z ∈ V, (∀ i, z i ∈ Kα β) → z = z 0 • v := by
      intro β hβ z hz hzβ
      refine sub_eq_zero.mp (hzero _ (V.sub_mem hz (V.smul_mem _ hvV)) ?_ fun i => ?_)
      · simp [hv0]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact sub_mem (hβ (hzβ i)) (mul_mem (hβ (hzβ 0)) (hvα i))
    have hvβ : ∀ β, Kα β ≤ Kα α → ∀ i, v i ∈ Kα β := by
      intro β hβ i
      obtain ⟨z, hzV, hz0, hzβ⟩ := h β
      have hz := hmult β hβ z hzV hzβ
      have hz1 : z 0 ≠ 0 := fun h0 => hz0 (by rw [hz, h0, zero_smul])
      have hzi : z i = z 0 * v i := by
        conv_lhs => rw [hz]
        rfl
      have : v i = (z 0)⁻¹ * z i := by rw [hzi, ← mul_assoc, inv_mul_cancel₀ hz1, one_mul]
      rw [this]; exact mul_mem (inv_mem (hzβ 0)) (hzβ i)
    refine ⟨v, hvV, fun h0 => by simp [h0] at hv0, fun i => ?_⟩
    have hmem : v i ∈ ⨅ γ, Kα γ := by
      rw [← SetLike.mem_coe, IntermediateField.coe_iInf, Set.mem_iInter]
      intro γ
      obtain ⟨δ, hδ⟩ := hdir α γ
      exact (hδ.trans inf_le_right) (hvβ δ (hδ.trans inf_le_left) i)
    rw [hinf, IntermediateField.mem_bot] at hmem
    exact hmem
