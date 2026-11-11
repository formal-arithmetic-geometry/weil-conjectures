/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity
public import WeilConjectures.WeilSheaf.CurveTopCohomology

/-!
# Weights of `H⁰` and of `H_c²` of a lisse Weil sheaf on a curve

Let `F` be a Weil sheaf on a `k₀`-scheme `X₀` of finite type over `k₀ = 𝔽_q`. Every eigenvalue
`β` of the Frobenius on the global sections `H⁰(X, F)` is, up to the power `deg x`, a local
Frobenius eigenvalue of `F` at a closed point `x`
(`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections`). So if
`F` is punctually of weights `≤ a`, or punctually pure of weight `a`, then so is `H⁰(X, F)`.

If `X₀` is a smooth curve and `F` is lisse, then `H_c²(X, F) = V_{π₁(X)}(-1)` is the Tate twist of
the dual of `H⁰(X, F^∨)` by Poincaré duality. The eigenvalues of the Frobenius on `H⁰(X, F^∨)` are,
up to powers, inverses of local eigenvalues of `F`, so the weights of `H_c²(X, F)` are at most
`a + 2` when `F` is punctually of weights `≤ a`, and `H_c²(X, F)` is pure of weight `a + 2` when
`F` is punctually pure of weight `a`. Neither affineness nor geometric connectedness of `X₀` is
needed here.

## Main statements

- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.hasWeightsAtMostOver_globalSections`: blueprint
  `lemma-degree-zero-top-cohomology--5`.
- `HasWeightsAtMost.hasWeightsAtMostOver_compactlySupportedCohomology_two`: blueprint
  `lemma-degree-zero-top-cohomology--6`.
- `IsPunctuallyPureOfWeight.isPureOfWeightOver_globalSections_and_compactlySupportedCohomology_two`:
  blueprint `lemma-degree-zero-top-cohomology--7`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {ι : PadicAlgCl l →+* ℂ}

/-- Blueprint `lemma-degree-zero-top-cohomology--5`: if `F` is punctually of weights `≤ a`, the
weights of `H⁰(X, F)` are at most `a`.

Every eigenvalue `β` of the Frobenius on the global sections is, up to the power `deg x`, a local
Frobenius eigenvalue of `F` at some closed point `x`
(`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections`). This
holds on any `k₀`-scheme of finite type, without smoothness or lissity. -/
theorem HasWeightsAtMost.hasWeightsAtMostOver_globalSections {F : WeilSheaf k₀ l X} {a : ℝ}
    (hF : F.HasWeightsAtMost ι a) : F.globalSections.HasWeightsAtMostOver k₀ ι a := by
  intro β hβ
  obtain ⟨x, hx⟩ := exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections F hβ
  have h := hF x _ hx
  have hm := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  rw [map_pow, norm_pow, Scheme.Hom.residueCard, Nat.cast_pow, ← Real.rpow_natCast_mul hq,
    mul_comm, Real.rpow_mul_natCast hq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg hq _) hm).1 h

/-- If `F` is punctually `ι`-pure of weight `a`, then `H⁰(X, F)` is `ι`-pure of weight `a`
(possibly zero): every Frobenius eigenvalue on the global sections is, up to the power `deg x`, a
local Frobenius eigenvalue of `F` at some closed point `x`. -/
theorem IsPunctuallyPureOfWeight.isPureOfWeightOver_globalSections {F : WeilSheaf k₀ l X}
    {a : ℝ} (hF : F.IsPunctuallyPureOfWeight ι a) :
    F.globalSections.IsPureOfWeightOver k₀ ι a := by
  intro β hβ
  obtain ⟨x, hx⟩ := exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections F hβ
  have h := hF x _ hx
  have hm := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  rw [map_pow, norm_pow, Scheme.Hom.residueCard, Nat.cast_pow, ← Real.rpow_natCast_mul hq,
    mul_comm, Real.rpow_mul_natCast hq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hq _) hm).1 h

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]

/-- `H_c²(X, F) ≃ V_{π₁(X)}(-1)` for a lisse Weil sheaf `F` on a smooth curve `X₀`, not
necessarily affine or geometrically connected: the proof of
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`, by Poincaré duality
`H_c²(X, F) ≃ H⁰(X, F^∨)^∨(-1)`, only uses that `X₀` is a smooth curve. -/
theorem nonempty_equiv_compactlySupportedCohomology_two_of_isLisse (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) :
    Nonempty ((F.compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) := by
  obtain ⟨P, hP, hPF⟩ :=
    exists_isPerfPair_compactlySupportedCohomology_dual_mul 1 F hF 2 0 (by norm_num)
  have hq : (Nat.card k₀ : PadicAlgCl l) ^ (-(-1 : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  exact ⟨(FrobeniusModule.Equiv.ofIsPerfPair P hq fun x y ↦ by
    rw [hPF, neg_neg, zpow_one, pow_one]).trans
      ((cohomologyZeroEquiv (F.dual hF)).dual.rescale _)⟩

/-- Blueprint `lemma-degree-zero-top-cohomology--6`: if `F` is punctually of weights `≤ a`, the
weights of `H_c²(X, F)` are at most `a + 2`.

Here `X₀` is a smooth curve and `F` is lisse. By Poincaré duality
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two_of_isLisse`) an
eigenvalue of the Frobenius on `H_c²(X, F)` is `q β` for an eigenvalue `β` on the geometric
coinvariants, which have weights at most `a`
(`AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_geometricCoinvariants`). -/
theorem HasWeightsAtMost.hasWeightsAtMostOver_compactlySupportedCohomology_two
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) {a : ℝ} (hw : F.HasWeightsAtMost ι a) :
    (F.compactlySupportedCohomology 2).HasWeightsAtMostOver k₀ ι (a + 2) := by
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_two_of_isLisse F hF
  have hq : (0 : ℝ) < Nat.card k₀ := by exact_mod_cast Nat.card_pos
  have hc : (Nat.card k₀ : PadicAlgCl l) ^ (-(-1 : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  intro α hα
  obtain ⟨β, rfl⟩ : ∃ β, α = (Nat.card k₀ : PadicAlgCl l) ^ (-(-1 : ℤ)) * β :=
    ⟨((Nat.card k₀ : PadicAlgCl l) ^ (-(-1 : ℤ)))⁻¹ * α, by field_simp⟩
  have h₁ := (FrobeniusModule.hasEigenvalue_frobeniusEnd_rescale_iff hc β).1 (e.hasEigenvalue hα)
  have h₃ := hasWeightsAtMostOver_geometricCoinvariants ι hF hw β h₁
  have hcn : ‖ι ((Nat.card k₀ : PadicAlgCl l) ^ (-(-1 : ℤ)))‖ = Nat.card k₀ := by simp
  rw [map_mul, norm_mul, hcn]
  calc (Nat.card k₀ : ℝ) * ‖ι β‖ ≤ (Nat.card k₀ : ℝ) * (Nat.card k₀ : ℝ) ^ (a / 2) :=
        mul_le_mul_of_nonneg_left h₃ hq.le
    _ = (Nat.card k₀ : ℝ) ^ ((a + 2) / 2) := by
        rw [add_div, div_self two_ne_zero, Real.rpow_add_one hq.ne', mul_comm]

namespace IsPunctuallyPureOfWeight

/-- Blueprint `lemma-degree-zero-top-cohomology--7`: if `F` is pure of weight `a`, then `H⁰(X, F)`
and `H_c²(X, F)`, when nonzero, are pure of weights `a` and `a + 2`, respectively.

Here `X₀` is a smooth curve and `F` is lisse and punctually `ι`-pure of weight `a`. The statement
for `H⁰` is `IsPunctuallyPureOfWeight.isPureOfWeightOver_globalSections`.
For `H_c²`, Poincaré duality identifies it with the Tate twist `(-1)` of the geometric coinvariants
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two_of_isLisse`), which
are pure of weight `a` (`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`). -/
theorem isPureOfWeightOver_globalSections_and_compactlySupportedCohomology_two
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) {a : ℝ} (hw : F.IsPunctuallyPureOfWeight ι a) :
    F.globalSections.IsPureOfWeightOver k₀ ι a ∧
      (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (a + 2) := by
  refine ⟨hw.isPureOfWeightOver_globalSections, ?_⟩
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_two_of_isLisse F hF
  have h := (isPureOfWeightOver_geometricCoinvariants ι F hF hw).tateTwist Nat.card_pos (-1)
  have ha : a - 2 * ((-1 : ℤ) : ℝ) = a + 2 := by push_cast; ring
  rw [ha] at h
  exact FrobeniusModule.IsPureOfWeight.of_equiv e h

end IsPunctuallyPureOfWeight

end AlgebraicGeometry.WeilSheaf
