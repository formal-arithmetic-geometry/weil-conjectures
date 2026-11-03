/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedCoefficientTowers
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Topology.Algebra.Ring.Ideal

/-! # The actual finite discrete ell-power coefficient rings

Source: current blueprint sk-def-sp-coefficient-towers, coefficient convention.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open Topology
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

/-- The continuous ell-power quotient has finite carrier and discrete quotient topology,
and is killed by the indicated power of ell. This uses the actual ell-power ideal and
therefore also covers ramified extensions.

Source: sk-def-sp-coefficient-towers, finite coefficient convention; the normalization
step of sk-prop-sp-integral-adjunction (blueprint: lem-sp-ell-power-coefficient-stages).

Proof: ell is nonzero. Write it as a unit times a power of a uniformizer. Its
principal ideal is that power of the maximal ideal. The finite residue field and
finiteness of quotients by powers of a finitely generated ideal give finiteness. A nonzero principal
ideal contains the inverse image of a sufficiently small ball about zero: if the norm of
x is smaller than the norm of its generator a, then x/a is integral. Hence the ideal is
open and its quotient topology is discrete. Finally ell^(n+1) belongs to (ell)^(n+1), so
its image in the quotient vanishes. The positive exponent n+1 excludes the zero exponent
without assuming any unramifiedness. -/
theorem ellPowerCoefficientStages (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A := Padic.coefficientExtensionIntegers l E ⧸ ellIdeal l E ^ (n + 1)
    Finite A ∧ DiscreteTopology A ∧ (l ^ (n + 1) : A) = 0 := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let O := Padic.coefficientExtensionIntegers l E
  let J := ellIdeal l E ^ (n + 1)
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : CharZero E := Algebra.charZero_of_charZero ℚ_[l] E
  have hl : (l : O) ≠ 0 := by
    intro hz
    have hz' : (l : E) = 0 := congrArg Subtype.val hz
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) hz'
  have hfinite : Finite (O ⧸ J) := by
    let M := Padic.coefficientExtensionMaximalIdeal l E
    let : IsLocalRing O := h.2.2.2.1
    let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
    have hM : M = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (R := O) h.2.2.2.2.1
    let π := Padic.coefficientExtensionUniformizer l E
    have hπ : Ideal.span ({π} : Set O) = M :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hirr : Irreducible π :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hM.symm.trans hπ.symm)
    obtain ⟨r, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hirr
    have he : ellIdeal l E = M ^ r := by
      change Ideal.span ({(l : O)} : Set O) = M ^ r
      rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit,
        ← Ideal.span_singleton_pow, hπ]
    have : Finite (O ⧸ M) := h.2.2.2.2.2.2.2.2.2.2.2.1
    change Finite (O ⧸ ellIdeal l E ^ (n + 1))
    rw [he, ← pow_mul]
    exact Ideal.finite_quotient_pow (hπ ▸ Submodule.fg_span_singleton π) _
  refine ⟨hfinite, ?_, ?_⟩
  · change DiscreteTopology (O ⧸ J)
    apply QuotientAddGroup.discreteTopology_iff.mpr
    apply J.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    let a : O := (l : O) ^ (n + 1)
    have ha : (a : E) ≠ 0 := by
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
    have hball : {x : O | ‖(x : E)‖ < ‖(a : E)‖} ∈ 𝓝 (0 : O) := by
      exact (isOpen_lt continuous_subtype_val.norm continuous_const).mem_nhds
        (by
          change ‖((0 : O) : E)‖ < ‖(a : E)‖
          simpa only [Subring.coe_zero, norm_zero] using norm_pos_iff.mpr ha)
    apply Filter.mem_of_superset hball
    intro x hx
    change x ∈ J
    change x ∈ ellIdeal l E ^ (n + 1)
    rw [Ideal.span_singleton_pow]
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨⟨(x : E) / (a : E), ?_⟩, ?_⟩
    · apply (h.1 _).mpr
      change ‖(x : E) / (a : E)‖ ≤ 1
      rw [norm_div]
      exact (div_lt_one (norm_pos_iff.mpr ha)).mpr hx |>.le
    · apply Subtype.ext
      exact div_mul_cancel₀ _ ha
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (l : O))) _

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
