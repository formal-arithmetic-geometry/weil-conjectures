/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.NumberTheory.Padics.IntegersModPow

/-!
# The ring of integers `𝒪_E` as a `ℤ_ℓ`-module

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`, with ring of integers
`𝒪_E = PadicAlgCl.integers l E`. This file shows that `𝒪_E` is a finite free `ℤ_ℓ`-module,
topologically isomorphic to `ℤ_ℓʳ`, and that `E` is the localization of `𝒪_E` at `ℓ`.

## Main statements

- `PadicAlgCl.exists_pow_mul_mem_integers`: every `x ∈ E` has `ℓⁿ x ∈ 𝒪_E` for some `n`.
- `PadicAlgCl.finite_integersPadicIntHom`, `PadicAlgCl.free_integersPadicIntHom`: `𝒪_E` is a
  finite free `ℤ_ℓ`-module.
- `PadicAlgCl.exists_continuousAddEquiv_integers`: `𝒪_E ≃ₜ+ ℤ_ℓʳ` for some `r`.
- `PadicAlgCl.isLocalizedModule_integers_subtype`: the inclusion `𝒪_E → E` is the localization
  of abelian groups at the powers of `ℓ`.
-/

@[expose] public section

open NNReal

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

/-- Every element of a subfield `E` of `ℚ̄_ℓ` lies in `𝒪_E` after multiplication by a power
of `ℓ`. -/
lemma exists_pow_mul_mem_integers (x : E) : ∃ n : ℕ, (l : E) ^ n * x ∈ integers l E := by
  let := normedFieldOfAlgebra l E
  have hl0 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖x‖ + 1) by positivity)
    (inv_lt_one_of_one_lt₀ hl0)
  refine ⟨n, ?_⟩
  rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm]
  change ‖(l : E) ^ n * x‖ ≤ 1
  rw [norm_mul, norm_pow, show ‖(l : E)‖ = (l : ℝ)⁻¹ from norm_algebraMap_natCast_self l E]
  rw [lt_div_iff₀ (by positivity)] at hn
  nlinarith [norm_nonneg x, pow_nonneg (inv_nonneg.2 (zero_le_one.trans hl0.le)) n]

/-- **`E` is the localization of `𝒪_E` at `ℓ`.** The inclusion `𝒪_E → E`, as a map of abelian
groups, inverts `ℓ`: `ℓ` acts invertibly on `E`, and every element of `E` is `ℓ⁻ⁿ x` for some
`x ∈ 𝒪_E`. -/
theorem isLocalizedModule_integers_subtype :
    IsLocalizedModule (Submonoid.powers (l : ℤ))
      (integers l E).subtype.toAddMonoidHom.toIntLinearMap := by
  have hl : (l : E) ≠ 0 := by
    have : CharZero E := (algebraMap E (PadicAlgCl l)).charZero
    exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine ⟨fun ⟨_, n, rfl⟩ ↦ ?_, fun y ↦ ?_, fun {x₁ x₂} h ↦ ⟨1, ?_⟩⟩
  · rw [Module.End.isUnit_iff]
    have : ⇑(algebraMap ℤ (Module.End ℤ E) ((l : ℤ) ^ n)) = ((l : E) ^ n * ·) := by
      ext x
      rw [Module.algebraMap_end_apply]
      simp
    rw [this]
    exact mulLeft_bijective₀ _ (pow_ne_zero n hl)
  · obtain ⟨n, hn⟩ := exists_pow_mul_mem_integers l E y
    refine ⟨(⟨_, hn⟩, ⟨(l : ℤ) ^ n, n, rfl⟩), ?_⟩
    rw [Submonoid.smul_def]
    simp
  · simpa using Subtype.ext h

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- `𝒪_E` is a finite `ℤ_ℓ`-module: the coordinates in a `ℚ_ℓ`-basis of `E` are continuous,
hence bounded on the compact `𝒪_E`, so that `x ↦ (ℓ^N c_i(x))_i` embeds `𝒪_E` into `ℤ_ℓⁿ`. -/
theorem finite_integersPadicIntHom :
    letI := (integersPadicIntHom l E).toAlgebra
    Module.Finite ℤ_[l] (integers l E) := by
  let := (integersPadicIntHom l E).toAlgebra
  let := normedFieldOfAlgebra l E
  have := compactSpace_integers l E
  let : NormedSpace ℚ_[l] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl l) (c • x)‖ ≤ ‖c‖ * ‖algebraMap E (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let b := Module.finBasis ℚ_[l] E
  have hcont : Continuous fun x : integers l E ↦ b.equivFun x :=
    (LinearMap.continuous_of_finiteDimensional b.equivFun.toLinearMap).comp
      continuous_subtype_val
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  have hl0 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (|C| + 1) by positivity)
    (inv_lt_one_of_one_lt₀ hl0)
  have hmem (x : integers l E) (i : Fin (Module.finrank ℚ_[l] E)) :
      (l : ℚ_[l]) ^ N * b.equivFun x i ∈ PadicInt.subring l := by
    have h₁ : ‖b.equivFun x i‖ ≤ |C| :=
      (norm_le_pi_norm _ i).trans ((hC x (Set.mem_univ _)).trans (le_abs_self C))
    rw [PadicInt.mem_subring_iff, norm_mul, norm_pow, Padic.norm_p]
    rw [lt_div_iff₀ (by positivity)] at hN
    nlinarith [norm_nonneg (b.equivFun x i),
      pow_nonneg (inv_nonneg.2 (zero_le_one.trans hl0.le)) N]
  let T : integers l E →ₗ[ℤ_[l]] (Fin (Module.finrank ℚ_[l] E) → ℤ_[l]) :=
    { toFun x i := (⟨(l : ℚ_[l]) ^ N * b.equivFun x i, hmem x i⟩ : ℤ_[l])
      map_add' x y := funext fun i ↦ PadicInt.ext <|
        (congrArg ((l : ℚ_[l]) ^ N * ·) (by simp)).trans (mul_add _ _ _)
      map_smul' z x := funext fun i ↦ PadicInt.ext <| by
        have h : b.equivFun ((z • x : integers l E) : E) i = (z : ℚ_[l]) * b.equivFun x i := by
          rw [← smul_eq_mul, ← Pi.smul_apply, ← map_smul]
          exact congrArg (b.equivFun · i) (Algebra.smul_def _ _).symm
        exact (congrArg ((l : ℚ_[l]) ^ N * ·) h).trans (mul_left_comm _ _ _) }
  have hT : Function.Injective T := by
    intro x y hxy
    refine Subtype.ext (b.equivFun.injective (funext fun i ↦ ?_))
    have := congrArg (fun z ↦ (z i : ℚ_[l])) hxy
    exact mul_left_cancel₀ (pow_ne_zero N (by exact_mod_cast (Fact.out : l.Prime).ne_zero)) this
  have := isNoetherian_of_injective T hT
  infer_instance

/-- `𝒪_E` is a free `ℤ_ℓ`-module, being finite and torsion free over the principal ideal domain
`ℤ_ℓ`. -/
theorem free_integersPadicIntHom :
    letI := (integersPadicIntHom l E).toAlgebra
    Module.Free ℤ_[l] (integers l E) := by
  let := (integersPadicIntHom l E).toAlgebra
  have := finite_integersPadicIntHom l E
  have : Module.IsTorsionFree ℤ_[l] (integers l E) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.algebraMap_toAlgebra]
    intro a b h
    have h' := congrArg (algebraMap (integers l E) (PadicAlgCl l)) h
    rw [algebraMap_integersPadicIntHom, algebraMap_integersPadicIntHom] at h'
    exact PadicInt.ext ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h')
  exact Module.free_of_finite_type_torsion_free'

/-- **`𝒪_E ≅ ℤ_ℓʳ` topologically.** The ring of integers of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
is isomorphic, as a topological group, to `ℤ_ℓʳ`: the coordinates in a `ℤ_ℓ`-basis form a
continuous bijection `ℤ_ℓʳ → 𝒪_E` from a compact space to a Hausdorff space. -/
theorem exists_continuousAddEquiv_integers :
    letI := normedFieldOfAlgebra l E
    ∃ r : ℕ, Nonempty (integers l E ≃ₜ+ (Fin r → ℤ_[l])) := by
  let := normedFieldOfAlgebra l E
  let := (integersPadicIntHom l E).toAlgebra
  have := finite_integersPadicIntHom l E
  have := free_integersPadicIntHom l E
  have := compactSpace_integers l E
  have := isTopologicalRing_integers l E
  let b := Module.finBasis ℤ_[l] (integers l E)
  have hcont : Continuous b.equivFun.symm := by
    have : (b.equivFun.symm : (Fin _ → ℤ_[l]) → integers l E) =
        fun c ↦ ∑ i, integersPadicIntHom l E (c i) * b i := by
      ext c
      simp [Module.Basis.equivFun_symm_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rw [this]
    exact continuous_finsetSum _ fun i _ ↦
      ((continuous_integersPadicIntHom l E).comp (continuous_apply i)).mul continuous_const
  let h := hcont.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)
  exact ⟨_, ⟨{ b.equivFun.toAddEquiv with
    continuous_toFun := h.symm.continuous
    continuous_invFun := h.continuous }⟩⟩

end PadicAlgCl
