/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.Algebra.Colimit.TensorProduct

/-!
# Equational criterion for vanishing, without a spanning hypothesis

`TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero` shows that a vanishing expression
$\sum_i m_i \otimes n_i = 0$ in $M \otimes_R N$ vanishes trivially provided the $m_i$ generate $M$.
Here we remove the generation hypothesis at the cost of enlarging the family: any vanishing
expression becomes trivially vanishing after adjoining finitely many auxiliary elements of $M$,
paired with the zero element of $N$.

The auxiliary elements really are needed. Take $R = \mathbb{Z}$, $M = \mathbb{Z}$,
$N = \mathbb{Z}/2$ and the one-element family $m_1 = 2$, $n_1 = 1$. Then
$2 \otimes 1 = 1 \otimes 2 = 0$, but $\sum_j a_{1j} m_1 = 0$ forces every $a_{1j} = 0$ and hence
$\sum_j a_{1j} y_j = 0 \neq n_1$, so the expression does not vanish trivially. Adjoining
$m' = 1$ paired with $0$ repairs this: take $y_1 = 1$, $a_{11} = 1$ and $a_{21} = -2$.

## Main results

- `TensorProduct.vanishesTrivially_comp_iff`: `VanishesTrivially` is preserved and reflected by
  an injective linear map applied to the first family.
- `TensorProduct.exists_vanishesTrivially_sum_elim_of_sum_tmul_eq_zero`: if
  $\sum_i m_i \otimes n_i = 0$ in $M \otimes_R N$, then the family becomes trivially vanishing
  after adjoining finitely many auxiliary elements of $M$ paired with $0 \in N$.
- `TensorProduct.vanishesTrivially_sum_elim_iff_sum_tmul_eq_zero`: the resulting criterion, as an
  iff. Unlike the criteria in `Mathlib/LinearAlgebra/TensorProduct/Vanishing.lean`, it holds with
  no hypothesis on $m$, $n$, $M$ or $N$.

## References

* [A. Altman and S. Kleiman, *A term of commutative algebra* (Lemma 8.16)][altman2021term]
* [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK)
-/

@[expose] public section

open Function LinearMap Submodule

namespace TensorProduct

variable (R : Type*) [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {ι : Type*} [Fintype ι] {m : ι → M} {n : ι → N}

/-- `VanishesTrivially` is preserved by pushing the first family forward along a linear map. -/
theorem VanishesTrivially.map {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')
    (h : VanishesTrivially R m n) : VanishesTrivially R (f ∘ m) n := by
  obtain ⟨k, a, y, h₁, h₂⟩ := h
  exact ⟨k, a, y, h₁, fun j ↦ by simpa using congrArg f (h₂ j)⟩

/-- `VanishesTrivially` is preserved and reflected by an injective linear map. -/
theorem vanishesTrivially_comp_iff {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M' →ₗ[R] M) (hf : Injective f) {m : ι → M'} :
    VanishesTrivially R (f ∘ m) n ↔ VanishesTrivially R m n := by
  refine ⟨fun h ↦ ?_, VanishesTrivially.map R f⟩
  obtain ⟨k, a, y, h₁, h₂⟩ := h
  refine ⟨k, a, y, h₁, fun j ↦ hf ?_⟩
  simpa using h₂ j

/-- **Equational criterion for vanishing**, forward direction, without a spanning hypothesis.

If $\sum_i m_i \otimes n_i = 0$ in $M \otimes_R N$, then there are finitely many auxiliary
elements $m'_1, \dots, m'_l$ of $M$ such that the enlarged family $(m, m')$, paired with
$(n, 0)$, vanishes trivially. Compare
`TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero`, which needs the $m_i$ to generate $M$.

The auxiliary elements cannot be dropped: over $R = \mathbb{Z}$ the expression
$2 \otimes 1 = 0$ in $\mathbb{Z} \otimes \mathbb{Z}/2$ does not vanish trivially. -/
theorem exists_vanishesTrivially_sum_elim_of_sum_tmul_eq_zero
    (hmn : ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N)) :
    ∃ (l : ℕ) (m' : Fin l → M), VanishesTrivially R (Sum.elim m m') (Sum.elim n 0) := by
  classical
  -- The expression already vanishes in $P \otimes N$ for $P$ the span of the $m_i$, ...
  have hmP i : m i ∈ span R (Set.range m) := subset_span ⟨i, rfl⟩
  have ht : rTensor N (span R (Set.range m)).subtype (∑ i, ⟨m i, hmP i⟩ ⊗ₜ[R] n i) =
      rTensor N (span R (Set.range m)).subtype 0 := by simp [hmn]
  -- ... hence in $Q \otimes N$ for some finitely generated $Q \supseteq P$.
  obtain ⟨Q, ⟨s, hs⟩, hPQ, hQ0⟩ := (fg_span (Set.finite_range m)).exists_rTensor_fg_inclusion_eq ht
  -- Adjoining a finite generating set `s` of `Q` makes the enlarged family generate `Q`.
  have hsQ (x : s) : (x : M) ∈ Q := hs ▸ subset_span x.2
  set M₀ : ι ⊕ Fin s.card → Q :=
    Sum.elim (fun i ↦ inclusion hPQ ⟨m i, hmP i⟩) fun t ↦ ⟨_, hsQ (s.equivFin.symm t)⟩ with hM₀
  have hspan : span R (Set.range M₀) = ⊤ := by
    apply map_injective_of_injective Q.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, range_subtype, ← Set.range_comp]
    refine le_antisymm (span_le.mpr ?_) (hs.ge.trans (span_le.mpr fun x hx ↦
      subset_span ⟨Sum.inr (s.equivFin ⟨x, hx⟩), by simp [hM₀]⟩))
    rintro _ ⟨(i | t), rfl⟩
    · exact hPQ (hmP i)
    · exact hsQ _
  have hsum : ∑ p, M₀ p ⊗ₜ[R] Sum.elim n 0 p = (0 : Q ⊗[R] N) := by
    rw [Fintype.sum_sum_type]
    simpa [hM₀] using hQ0
  have heq : Sum.elim m (fun t ↦ ((s.equivFin.symm t : s) : M)) = ⇑Q.subtype ∘ M₀ := by
    funext p; obtain (i | t) := p <;> simp [hM₀]
  refine ⟨s.card, fun t ↦ ((s.equivFin.symm t : s) : M), heq ▸ ?_⟩
  exact (vanishesTrivially_comp_iff R Q.subtype Q.injective_subtype).mpr
    (vanishesTrivially_of_sum_tmul_eq_zero R hspan hsum)

/-- **Equational criterion for vanishing**, without a spanning hypothesis.

The expression $\sum_i m_i \otimes n_i$ vanishes in $M \otimes_R N$ if and only if the family
$(m_i)$ becomes trivially vanishing, paired with $(n_i)$, after adjoining finitely many
auxiliary elements of $M$ paired with $0 \in N$. -/
theorem vanishesTrivially_sum_elim_iff_sum_tmul_eq_zero :
    (∃ (l : ℕ) (m' : Fin l → M), VanishesTrivially R (Sum.elim m m') (Sum.elim n 0)) ↔
      ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) := by
  refine ⟨fun ⟨l, m', h⟩ ↦ ?_, exists_vanishesTrivially_sum_elim_of_sum_tmul_eq_zero R⟩
  simpa [Fintype.sum_sum_type] using sum_tmul_eq_zero_of_vanishesTrivially R h

end TensorProduct
