/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin
public import WeilConjectures.RepresentationTheory.TensorPower

/-!
# Determinant weights of tensor powers and exterior powers

Let `ρ` be a nonzero lisse Weil sheaf on a smooth geometrically connected curve `C₀ / 𝔽_q`, with
determinantal-weight multiset `α₁, …, αₙ` (`AlgebraicGeometry.WeilGroup.detWeightMultiset`). By
rank-one purity every lisse sheaf has finite geometric determinant and its determinant weight
`dw_ι` is the determinant weight `dw_{λ_ι}` for the real weight character `λ_ι`
(`lem-rp-determinant-weights-agree`), so the representation-theoretic weight rules of
`sec-algebraic-groups-lie-algebras` apply. This file deduces from the two-factor tensor rule
(`prop-ag-det-weight-two-factor-tensor`) that the determinant weights of the constituents of the
tensor power `ρ^{⊗ k}` are exactly the sums `α_{i₁} + ⋯ + α_{i_k}`.

## Main statements

- `AlgebraicGeometry.WeilGroup.IsLisse.tensorPower`: tensor powers of lisse sheaves are lisse.
- `AlgebraicGeometry.WeilGroup.detWeight_subquotient_tensorPower`: the determinant weights of
  the constituents of `ρ^{⊗ k}` (blueprint `cor-mg-det-weight-finite-tensor`).
- `AlgebraicGeometry.WeilGroup.isGreatest_detWeight_subquotient_tensorPower`: the largest one is
  `k β` for the largest determinant weight `β` of `ρ`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  {ρ : Representation (PadicAlgCl l) W.carrier V} (ι : PadicAlgCl l →+* ℂ)

/-- Tensor powers `ρ^{⊗ n}`, `n ≥ 1`, of a lisse Weil sheaf are lisse. -/
theorem IsLisse.tensorPower (hρ : W.IsLisse l ρ) {n : ℕ} (hn : 1 ≤ n) :
    W.IsLisse l (ρ.tensorPower n) := by
  induction n, hn using Nat.le_induction with
  | base => exact IsLisse.of_equiv ρ.tensorPowerOneEquiv.symm hρ
  | succ n hn ih => exact IsLisse.of_equiv (ρ.tensorPowerSuccEquiv n).symm (ih.tprod hρ)

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The determinant weight `dw_ι` is the determinant weight of `sk-d-weights` for the real weight
character `λ_ι = wt_{ι, q}` and the chosen Frobenius lift. -/
theorem detWeight_eq_detWeight_weightCharacter (σ : Representation (PadicAlgCl l) W.carrier V) :
    W.detWeight l σ ι = σ.detWeight (weightCharacter ι (Nat.card K)) W.frobeniusLift :=
  (detWeight_weightCharacter ι σ _ _).symm

variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
  [W.IsEtaleQuotient]

/-- Blueprint `cor-mg-det-weight-finite-tensor`: Determinant weights of a finite tensor power.

Let `ρ` be a lisse Weil sheaf, with determinantal-weight multiset `α₁, …, αₙ`, and `k ≥ 1`.
Every constituent `S / U` of the tensor power `ρ^{⊗ k}` has determinant weight
`α_{i₁} + ⋯ + α_{i_k}` for some indices `i₁, …, i_k` (that is, the sum of a multiset of `k`
entries of the determinantal-weight multiset, with repetitions allowed), and every such sum
occurs for some constituent. The proof is the induction of the blueprint on `k`, using
`ρ^{⊗ (k + 1)} ≅ ρ^{⊗ k} ⊗ ρ` and the two-factor tensor rule
(`Representation.exists_detWeight_eq_add_of_subquotient_tprod` and its converse
`Representation.exists_isIrreducible_subquotient_tprod_detWeight_eq_add`), whose finite
geometric determinant hypotheses hold by `lem-rp-determinant-weights-agree`. The geometric
semisimplicity assumed in the blueprint is not needed. -/
theorem detWeight_subquotient_tensorPower (hρ : W.IsLisse l ρ) {n : ℕ} (hn : 1 ≤ n) :
    (∀ U S : Subrepresentation (ρ.tensorPower n), (S.subquotient U).IsIrreducible →
      ∃ s : Multiset ℝ, Multiset.card s = n ∧ (∀ a ∈ s, a ∈ W.detWeightMultiset l ρ ι) ∧
        W.detWeight l (S.subquotient U) ι = s.sum) ∧
    ∀ s : Multiset ℝ, Multiset.card s = n → (∀ a ∈ s, a ∈ W.detWeightMultiset l ρ ι) →
      ∃ U S : Subrepresentation (ρ.tensorPower n), (S.subquotient U).IsIrreducible ∧
        W.detWeight l (S.subquotient U) ι = s.sum := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨fun U S hirr ↦ ?_, fun s hs hmem ↦ ?_⟩
    · obtain ⟨U', S', ⟨f⟩⟩ :=
        Subrepresentation.exists_subquotient_equiv_of_equiv ρ.tensorPowerOneEquiv.symm U S
      refine ⟨{W.detWeight l (S.subquotient U) ι}, Multiset.card_singleton _, fun a ha ↦ ?_,
        (Multiset.sum_singleton _).symm⟩
      rw [Multiset.mem_singleton.1 ha, detWeight_of_equiv ι f]
      exact (mem_detWeightMultiset_iff ι).2 ⟨U', S', f.isIrreducible_iff.2 hirr, rfl⟩
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hs
      obtain ⟨U, S, hirr, ha⟩ :=
        (mem_detWeightMultiset_iff ι).1 (hmem a (Multiset.mem_singleton_self a))
      obtain ⟨U', S', ⟨f⟩⟩ :=
        Subrepresentation.exists_subquotient_equiv_of_equiv ρ.tensorPowerOneEquiv U S
      exact ⟨U', S', f.isIrreducible_iff.2 hirr, by
        rw [Multiset.sum_singleton, ← ha, detWeight_of_equiv ι f]⟩
  | succ n hn ih =>
    have hlisse := hρ.tensorPower hn
    have hdetV (UV SV : Subrepresentation (ρ.tensorPower n)) :
        (SV.subquotient UV).HasFiniteGeometricDet W.deg :=
      (hasFiniteGeometricDet_and_detWeight_eq ι (hlisse.subquotient SV UV)).1
    have hdetE (UE SE : Subrepresentation ρ) : (SE.subquotient UE).HasFiniteGeometricDet W.deg :=
      (hasFiniteGeometricDet_and_detWeight_eq ι (hρ.subquotient SE UE)).1
    have hdet (U S : Subrepresentation ((ρ.tensorPower n).tprod ρ)) :
        (S.subquotient U).HasFiniteGeometricDet W.deg :=
      (hasFiniteGeometricDet_and_detWeight_eq ι ((hlisse.tprod hρ).subquotient S U)).1
    refine ⟨fun U S hirr ↦ ?_, fun s hs hmem ↦ ?_⟩
    · obtain ⟨U', S', ⟨f⟩⟩ :=
        Subrepresentation.exists_subquotient_equiv_of_equiv (ρ.tensorPowerSuccEquiv n).symm U S
      obtain ⟨UV, SV, UE, SE, -, -, hV, hE, -, -, heq⟩ :=
        Representation.exists_detWeight_eq_add_of_subquotient_tprod
          (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift (ρ.tensorPower n) ρ
          (fun UV SV _ ↦ hdetV UV SV) (fun UE SE _ ↦ hdetE UE SE)
          (f.isIrreducible_iff.2 hirr) (hdet U' S')
      obtain ⟨s, hs, hmem, hsum⟩ := ih.1 UV SV hV
      refine ⟨W.detWeight l (SE.subquotient UE) ι ::ₘ s, by rw [Multiset.card_cons, hs],
        fun a ha ↦ ?_, ?_⟩
      · rcases Multiset.mem_cons.1 ha with rfl | ha
        · exact (mem_detWeightMultiset_iff ι).2 ⟨UE, SE, hE, rfl⟩
        · exact hmem a ha
      · rw [Multiset.sum_cons, ← hsum, detWeight_of_equiv ι f,
          detWeight_eq_detWeight_weightCharacter, heq, detWeight_eq_detWeight_weightCharacter,
          detWeight_eq_detWeight_weightCharacter, add_comm]
    · obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hs]; exact Nat.succ_pos n)
      obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
      rw [Multiset.card_cons, Nat.add_right_cancel_iff] at hs
      obtain ⟨UV, SV, hV, hsum⟩ :=
        ih.2 s hs fun b hb ↦ hmem b (Multiset.mem_cons_of_mem hb)
      obtain ⟨UE, SE, hE, ha'⟩ :=
        (mem_detWeightMultiset_iff ι).1 (hmem a (Multiset.mem_cons_self a s))
      obtain ⟨U, S, -, hirr, heq⟩ :=
        Representation.exists_isIrreducible_subquotient_tprod_detWeight_eq_add
          (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift hV hE (hdetV UV SV)
          (hdetE UE SE) fun U S _ ↦ hdet U S
      obtain ⟨U', S', ⟨f⟩⟩ :=
        Subrepresentation.exists_subquotient_equiv_of_equiv (ρ.tensorPowerSuccEquiv n) U S
      refine ⟨U', S', f.isIrreducible_iff.2 hirr, ?_⟩
      rw [Multiset.sum_cons, ← hsum, ← ha', ← detWeight_of_equiv ι f,
        detWeight_eq_detWeight_weightCharacter, heq, detWeight_eq_detWeight_weightCharacter,
        detWeight_eq_detWeight_weightCharacter, add_comm]

/-- Blueprint `cor-mg-det-weight-finite-tensor`: Determinant weights of a finite tensor power.

If `β` is the largest determinant weight of the lisse Weil sheaf `ρ`, then the largest
determinant weight of a constituent of `ρ^{⊗ k}`, `k ≥ 1`, is `k β`. -/
theorem isGreatest_detWeight_subquotient_tensorPower (hρ : W.IsLisse l ρ) {n : ℕ} (hn : 1 ≤ n)
    {β : ℝ} (hβ : IsGreatest {a | a ∈ W.detWeightMultiset l ρ ι} β) :
    IsGreatest {x | ∃ U S : Subrepresentation (ρ.tensorPower n),
      (S.subquotient U).IsIrreducible ∧ W.detWeight l (S.subquotient U) ι = x} (n * β) := by
  obtain ⟨h₁, h₂⟩ := detWeight_subquotient_tensorPower ι hρ hn
  refine ⟨?_, ?_⟩
  · obtain ⟨U, S, hirr, hsum⟩ := h₂ (Multiset.replicate n β) (Multiset.card_replicate n β)
      fun a ha ↦ (Multiset.eq_of_mem_replicate ha) ▸ hβ.1
    exact ⟨U, S, hirr, by rw [hsum, Multiset.sum_replicate, nsmul_eq_mul]⟩
  · rintro x ⟨U, S, hirr, rfl⟩
    obtain ⟨s, hs, hmem, hsum⟩ := h₁ U S hirr
    rw [hsum, ← hs, ← nsmul_eq_mul]
    exact Multiset.sum_le_card_nsmul s β fun a ha ↦ hβ.2 (hmem a ha)

end WeilGroup

end AlgebraicGeometry
