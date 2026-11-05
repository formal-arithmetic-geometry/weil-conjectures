/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.NumberTheory.Padics.Logarithm

/-!
# The reductions `𝒪_E ⧸ ℓⁿ` of the ring of integers of a subfield of `ℚ̄_ℓ`

Let `E` be a subfield of `ℚ̄_ℓ = PadicAlgCl ℓ` with ring of integers
`𝒪_E = PadicAlgCl.integers ℓ E`, topologised as a subspace of `E` with the norm restricted from
`ℚ̄_ℓ` (`PadicAlgCl.normedFieldOfAlgebra`). This file sets up the discrete rings
`PadicAlgCl.integersModPow ℓ E n = 𝒪_E ⧸ ℓⁿ` with their reduction and transition maps, and proves
the topological facts saying that `𝒪_E` is the limit of the tower `n ↦ 𝒪_E ⧸ ℓⁿ` as a topological
ring:

- `PadicAlgCl.continuous_integersModPowMk`: the reductions are continuous;
- `PadicAlgCl.isEmbedding_natCast_pow_mul`: multiplication by `ℓⁿ` is an embedding, so that the
  kernel `ℓⁿ 𝒪_E` of the reduction is a homeomorphic copy of `𝒪_E`;
- `PadicAlgCl.integersModPowMk_injective`, `PadicAlgCl.exists_integersModPowMk_eq` and
  `PadicAlgCl.isInducing_integersModPowMk`: `𝒪_E → lim 𝒪_E ⧸ ℓⁿ` is bijective, the surjectivity
  using completeness for `E` finite over `ℚ_ℓ`, and `𝒪_E` carries the induced topology.

These are the hypotheses of the sheaf-theoretic statements of
`WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapReduction` for `R = 𝒪_E`.
-/

@[expose] public section

open Topology

namespace PadicAlgCl
variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

/-- The reduction `𝒪_E ⧸ ℓⁿ` of the ring of integers of a subfield `E ⊆ ℚ̄_ℓ`, with the discrete
topology. -/
def integersModPow (n : ℕ) : Type :=
  integers l E ⧸ Ideal.span {(l : integers l E) ^ n}

noncomputable instance (n : ℕ) : CommRing (integersModPow l E n) :=
  Ideal.Quotient.commRing _

instance (n : ℕ) : TopologicalSpace (integersModPow l E n) := ⊥

instance (n : ℕ) : DiscreteTopology (integersModPow l E n) := ⟨rfl⟩

instance (n : ℕ) : IsTopologicalRing (integersModPow l E n) :=
  DiscreteTopology.topologicalRing

/-- The reduction map `𝒪_E → 𝒪_E ⧸ ℓⁿ`. -/
noncomputable def integersModPowMk (n : ℕ) : integers l E →+* integersModPow l E n :=
  Ideal.Quotient.mk _

/-- The transition map `𝒪_E ⧸ ℓⁿ⁺¹ → 𝒪_E ⧸ ℓⁿ`. -/
noncomputable def integersModPowTransition (n : ℕ) :
    integersModPow l E (n + 1) →+* integersModPow l E n :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ n.le_succ))

lemma integersModPowMk_surjective (n : ℕ) : Function.Surjective (integersModPowMk l E n) :=
  Ideal.Quotient.mk_surjective

/-- The norm of `ℓ` in `E ⊆ ℚ̄_ℓ` is `ℓ⁻¹` (`norm_algebraMap_natCast` at `m = ℓ`). -/
lemma norm_algebraMap_natCast_self : ‖algebraMap E (PadicAlgCl l) (l : E)‖ = (l : ℝ)⁻¹ := by
  rw [norm_algebraMap_natCast, Padic.norm_p]

lemma integersModPowMk_eq_zero_iff (n : ℕ) (x : integers l E) :
    integersModPowMk l E n x = 0 ↔
      ‖algebraMap E (PadicAlgCl l) (x : E)‖ ≤ (l : ℝ)⁻¹ ^ n := by
  have hl : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
  refine Ideal.Quotient.eq_zero_iff_mem.trans (Ideal.mem_span_singleton'.trans ?_)
  constructor
  · rintro ⟨a, rfl⟩
    have ha : ‖algebraMap E (PadicAlgCl l) (a : E)‖ ≤ 1 := a.2
    have he : ((a * (l : integers l E) ^ n : integers l E) : E) = (a : E) * (l : E) ^ n := by
      simp
    rw [he]
    rw [map_mul, norm_mul, map_pow, norm_pow, norm_algebraMap_natCast_self]
    exact mul_le_of_le_one_left (pow_nonneg hl.le n) ha
  · intro hx
    have hl0 : (l : E) ≠ 0 := fun h ↦ by
      have := congrArg (algebraMap E (PadicAlgCl l)) h
      rw [map_natCast, map_zero] at this
      exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero this
    refine ⟨⟨(x : E) / (l : E) ^ n, ?_⟩, Subtype.ext ?_⟩
    · change ‖algebraMap E (PadicAlgCl l) ((x : E) / (l : E) ^ n)‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, coe_nnnorm, map_div₀, norm_div, map_pow, norm_pow,
        norm_algebraMap_natCast_self, NNReal.coe_one]
      exact div_le_one_of_le₀ hx (pow_nonneg hl.le n)
    · push_cast
      exact div_mul_cancel₀ _ (pow_ne_zero n hl0)

lemma integersModPowMk_eq_iff (n : ℕ) (x y : integers l E) :
    integersModPowMk l E n x = integersModPowMk l E n y ↔
      ‖algebraMap E (PadicAlgCl l) ((x : E) - y)‖ ≤ (l : ℝ)⁻¹ ^ n := by
  rw [← sub_eq_zero, ← map_sub, integersModPowMk_eq_zero_iff]
  rfl

lemma inv_prime_pos : (0 : ℝ) < (l : ℝ)⁻¹ :=
  inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)

lemma inv_prime_lt_one : (l : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

/-- The reduction maps `𝒪_E → 𝒪_E ⧸ ℓⁿ` are continuous: their fibres are closed balls, which are
open in the ultrametric space `𝒪_E`. -/
lemma continuous_integersModPowMk (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    Continuous (integersModPowMk l E n) := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  refine continuous_discrete_rng.2 fun q ↦ ?_
  obtain ⟨x, rfl⟩ := integersModPowMk_surjective l E n q
  have : integersModPowMk l E n ⁻¹' {integersModPowMk l E n x} =
      Subtype.val ⁻¹' Metric.closedBall (x : E) ((l : ℝ)⁻¹ ^ n) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm]
    exact integersModPowMk_eq_iff l E n y x
  rw [this]
  exact (IsUltrametricDist.isOpen_closedBall _ (pow_ne_zero _ (inv_prime_pos l).ne')).preimage
    continuous_subtype_val

/-- Multiplication by `ℓⁿ` on `𝒪_E` is an embedding, being the restriction of a homeomorphism
of `E`. -/
lemma isEmbedding_natCast_pow_mul (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    IsEmbedding (fun x : integers l E ↦ (l : integers l E) ^ n * x) := by
  let := normedFieldOfAlgebra l E
  have hc : (l : E) ^ n ≠ 0 := pow_ne_zero n (natCast_ne_zero_of_algebra (l := l) (E := E))
  refine (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).1 ?_
  have : Subtype.val ∘ (fun x : integers l E ↦ (l : integers l E) ^ n * x) =
      Homeomorph.mulLeft₀ ((l : E) ^ n) hc ∘ Subtype.val :=
    funext fun x ↦ by simp
  rw [this]
  exact (Homeomorph.mulLeft₀ _ hc).isEmbedding.comp IsEmbedding.subtypeVal

lemma exists_natCast_pow_mul_eq (n : ℕ) (x : integers l E) (hx : integersModPowMk l E n x = 0) :
    ∃ y, (l : integers l E) ^ n * y = x := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  exact ⟨a, (mul_comm _ _).trans ha⟩

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

end PadicAlgCl
