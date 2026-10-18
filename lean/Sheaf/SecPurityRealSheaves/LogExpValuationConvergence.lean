/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Valuation convergence of the deep p-adic logarithm and exponential

Source: literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/
`sk-d-real-log/lem-wf-deep-principal-unit-log.proof.md`, paragraphs 1--3
(blueprint: lem-wf-log-exp-valuation-convergence).

The normalized valuation is obtained from the unique unit--uniformizer decomposition
in the recorded finite-extension DVR. The deep ideal is the image in `E` of the
corresponding power of the recorded maximal ideal. The uniformity, topology and sums
are those of the recorded extending absolute value `coefficientExtensionAbsoluteValue`.

## Main definitions

* `Padic.coefficientExtensionValuation`: the normalized valuation `v_E`, `+∞` at zero.
* `Padic.coefficientExtensionRamificationIndex`: `e = v_E(ℓ)`.
* `Padic.coefficientExtensionDeepIdeal`: the ideal `𝔪_E^r` as a subset of `E`.
* `Padic.coefficientExtensionQ`, `Padic.coefficientExtensionDelta`,
  `Padic.coefficientExtensionTheta`: the constants `q`, `δ`, `θ`.

## Main statements

* `Padic.coefficientExtensionUnitDecomposition`: the unit--uniformizer decomposition.
* `Padic.valuation_convergence`: the valuation bounds and the uniform convergence,
  range and continuity of the logarithm and exponential series.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace Padic

/-- Unit--uniformizer decomposition for the selected finite-extension DVR.

Source: `lem-weil-l-adic-extension-integers-dvr`, specialized to the selected
coefficient-extension integer ring and uniformizer (blueprint:
lem-wf-log-exp-valuation-convergence).

Proof: apply the final decomposition clause of `extension_integers_dvr` to the
selected ring, maximal ideal, and uniformizer. Uniqueness is the DVR uniqueness
of the unit and exponent.
-/
theorem coefficientExtensionUnitDecomposition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (x : Eˣ) :
    ∃! p : (coefficientExtensionIntegers l E)ˣ × ℤ,
      (x : E) = ((p.1 : coefficientExtensionIntegers l E) : E) *
          (coefficientExtensionUniformizer l E : E) ^ p.2 := by
  sorry

/-- The normalized integer valuation, with `+∞` at zero.

Source: the normalized valuation attached to the selected uniformizer in
`lem-weil-l-adic-extension-integers-dvr` (blueprint:
lem-wf-log-exp-valuation-convergence).

The value at a nonzero element is the uniquely determined exponent in
`coefficientExtensionUnitDecomposition`; the value at zero is `+∞`.
-/
noncomputable def coefficientExtensionValuation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (x : E) : WithTop ℤ :=
  by
    classical
    exact if hx : x = 0 then ⊤ else
      ((Classical.choose (coefficientExtensionUnitDecomposition l E (Units.mk0 x hx))).2 :
      WithTop ℤ)

/-- The finite integer value of the normalized valuation away from zero.

Source: the normalized valuation convention in the blueprint
(blueprint: lem-wf-log-exp-valuation-convergence). -/
noncomputable def coefficientExtensionValuationInt
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (x : E) : ℤ :=
  WithTop.untopD 0 (coefficientExtensionValuation l E x)

/-- The ramification index `e = v_E(ℓ)` of a finite coefficient extension.

Source: the normalization in `lem-weil-l-adic-extension-integers-dvr` (blueprint:
lem-wf-log-exp-valuation-convergence).
-/
noncomputable def coefficientExtensionRamificationIndex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : ℤ :=
  WithTop.untopD 0
    (coefficientExtensionValuation l E (algebraMap (Padic l) E l))

/-- The image in `E` of the `r`-th power of the selected maximal ideal.

Source: the deep ideal `𝔪_E^r` in `lem-wf-deep-principal-unit-log`, paragraphs 1--2
(blueprint: lem-wf-log-exp-valuation-convergence).
-/
def coefficientExtensionDeepIdeal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (r : ℕ) : Set E :=
  {x | ∃ y : coefficientExtensionIntegers l E,
    (y : E) = x ∧ y ∈ (coefficientExtensionMaximalIdeal l E) ^ r}

/-- The uniformity induced by the recorded extending absolute value.

Source: `def-weil-l-adic-coefficient-extension` (blueprint:
`lem-wf-log-exp-valuation-convergence`). -/
@[instance_reducible]
noncomputable def coefficientExtensionUniformSpace
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : UniformSpace E :=
  (coefficientExtensionAbsoluteValue l E).toNormedField.toMetricSpace.toUniformSpace

/-- The topology induced by the canonical spectral absolute value.

Source: `def-weil-l-adic-coefficient-extension` (blueprint:
`lem-wf-log-exp-valuation-convergence`). -/
@[instance_reducible]
noncomputable def coefficientExtensionTopology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : TopologicalSpace E :=
  (coefficientExtensionUniformSpace l E).toTopologicalSpace

/-- The tsum in the canonical spectral norm topology on a finite coefficient extension.

Source: the spectral absolute value of `def-weil-l-adic-coefficient-extension`
(blueprint: `lem-wf-log-exp-valuation-convergence`). -/
noncomputable def coefficientExtensionTsum
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (f : ℕ → E) : E :=
  @tsum E ℕ _
    (coefficientExtensionTopology l E) f
    (SummationFilter.unconditional ℕ)

/-- The radius and geometric ratio used in the coefficient estimates.

Source: the definitions of `q`, `δ`, and `θ` in the blueprint proof
(blueprint: lem-wf-log-exp-valuation-convergence). -/
noncomputable def coefficientExtensionQ
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (r : ℕ) : ℝ :=
  (l : ℝ) ^ (-(r : ℝ) /
    (coefficientExtensionRamificationIndex l E : ℝ))

/-- The valuation gap `δ = r - e/(ℓ-1)` used in the geometric estimate.

Source: the definition of `δ` in the blueprint proof (blueprint:
`lem-wf-log-exp-valuation-convergence`). -/
noncomputable def coefficientExtensionDelta
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (r : ℕ) : ℝ :=
  (r : ℝ) - (coefficientExtensionRamificationIndex l E : ℝ) / ((l : ℝ) - 1)

/-- The geometric ratio `θ = ℓ^(-δ/e)` used in the coefficient estimate.

Source: the definition of `θ` in the blueprint proof (blueprint:
`lem-wf-log-exp-valuation-convergence`). -/
noncomputable def coefficientExtensionTheta
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (r : ℕ) : ℝ :=
  (l : ℝ) ^ (-coefficientExtensionDelta l E r /
    (coefficientExtensionRamificationIndex l E : ℝ))

/-- Valuation bounds and uniform convergence of the logarithm and exponential series on a
sufficiently deep ideal.

Source: literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/
`sk-d-real-log/lem-wf-deep-principal-unit-log.proof.md`, paragraphs 1--3
(blueprint: lem-wf-log-exp-valuation-convergence).

Proof:
1. By lem-weil-l-adic-extension-absolute-value the absolute value extends `|·|_ℓ` and is
   nonarchimedean. By lem-weil-l-adic-extension-integers-dvr write every nonzero `z` as
   `u ϖ^k` with `|u| = 1`, `k = v_E(z)`. As `|ℓ| = ℓ⁻¹ < 1`, `e > 0`; for `a ∈ ℚ_ℓ^×`,
   `v_E(a) = e v_ℓ(a)` (def-weil-l-adic-numbers). Also `𝔪_E^r = ϖ^r 𝒪_E`, so
   `z ∈ 𝔪_E^r` iff `z = 0` or `v_E(z) ≥ r`, iff `|z| ≤ q`.
2. lem-wf-legendre-digit-sum with `p = ℓ` and `s_ℓ(n) ≥ 1` gives
   `(ℓ-1) v_ℓ(n!) ≤ n-1`. For `k = v_ℓ(n)`, `ℓ^k ≤ n` and `ℓ^k ≥ 1 + k(ℓ-1)` by
   induction, so `(ℓ-1) v_ℓ(n) ≤ n-1`.
3. For `d = n` or `n!`, `|1/d| q^n = ℓ^(v_ℓ(d) - nr/e) ≤ q θ^(n-1)`; `r > e/(ℓ-1)` gives
   `δ > 0`, `q > 0` and `0 < θ < 1`.
4. For `x ≠ 0` in `𝔪_E^r`, lem-sc-dvr-valuation-arithmetic gives
   `v_E(x^n/d) = n v_E(x) - v_E(d) ≥ nr - e v_ℓ(d) ≥ r + (n-1)δ`; for `x = 0` the value
   is `⊤`. Hence `|x^n/d| ≤ q θ^(n-1)` on the disc.
5. By lem-wf-real-geometric-summability, `u_k = q θ^k` is summable and nonnegative.
6. `E` is complete (lem-weil-l-adic-extension-complete); the uniform-convergence clause
   of lem-wf-dominated-continuous-function-series (`tendstoUniformlyOn_tsum_nat`) with
   the bound `u_k` gives uniform convergence of both shifted families on `𝔪_E^r`.
7. Every term has `|·| ≤ q`; the ultrametric inequality bounds all partial sums and,
   in the limit, `|L(x)|, |A(x)| ≤ q`, so both sums lie in `𝔪_E^r` by step 1.
8. `|x^n - y^n| ≤ |x - y| q^(n-1)` on the disc, so every term is continuous; the
   continuity clause of lem-wf-dominated-continuous-function-series (`continuousOn_tsum`)
   gives continuity of `L` and `A`.
9. `exp(x) = 1 + A(x)`: adding the constant `1` preserves uniform convergence and
   continuity, and the range of `A` gives exponential values in `1 + 𝔪_E^r`.
-/
theorem valuation_convergence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (r : ℕ)
    (hr : (r : ℝ) >
      (coefficientExtensionRamificationIndex l E : ℝ) / ((l : ℝ) - 1)) :
    coefficientExtensionValuation l E 0 = ⊤ ∧
      coefficientExtensionAbsoluteValue l E 0 = 0 ∧
      (∀ x : E, x ≠ 0 →
        coefficientExtensionAbsoluteValue l E x =
          (l : ℝ) ^ (-(coefficientExtensionValuationInt l E x : ℝ) /
            (coefficientExtensionRamificationIndex l E : ℝ))) ∧
      (coefficientExtensionDeepIdeal l E 1 =
        {x : E | coefficientExtensionAbsoluteValue l E x < 1}) ∧
      (0 < coefficientExtensionRamificationIndex l E) ∧
      coefficientExtensionValuation l E (algebraMap (Padic l) E l) =
        (coefficientExtensionRamificationIndex l E : WithTop ℤ) ∧
      0 < coefficientExtensionDelta l E r ∧
      0 < coefficientExtensionQ l E r ∧
      0 < coefficientExtensionTheta l E r ∧
      coefficientExtensionTheta l E r < 1 ∧
      (∀ n : ℕ, 1 ≤ n →
        (padicValNat l n : ℝ) ≤ ((n : ℝ) - 1) / ((l : ℝ) - 1)) ∧
      (∀ n : ℕ, 1 ≤ n →
        (padicValNat l (Nat.factorial n) : ℝ) ≤ ((n : ℝ) - 1) / ((l : ℝ) - 1)) ∧
      (∀ x : E, x ∈ coefficientExtensionDeepIdeal l E r → ∀ n : ℕ, 1 ≤ n →
        coefficientExtensionValuation l E (x ^ n / (n : E)) ≥
          ((n : ℤ) * (r : ℤ) -
            coefficientExtensionRamificationIndex l E * (padicValNat l n : ℤ) : WithTop ℤ)) ∧
      (∀ x : E, x ∈ coefficientExtensionDeepIdeal l E r → ∀ n : ℕ, 1 ≤ n →
        WithTop.map (fun z : ℤ => (z : ℝ))
            (coefficientExtensionValuation l E (x ^ n / (n : E))) ≥
          ((((n : ℝ) * (r : ℝ) -
            (coefficientExtensionRamificationIndex l E : ℝ) *
              (padicValNat l n : ℝ)) : ℝ) : WithTop ℝ)) ∧
      (∀ x : E, x ∈ coefficientExtensionDeepIdeal l E r → ∀ n : ℕ, 1 ≤ n →
        WithTop.map (fun z : ℤ => (z : ℝ))
            (coefficientExtensionValuation l E (x ^ n / (n : E))) ≥
          (((r : ℝ) + ((n - 1 : ℕ) : ℝ) * coefficientExtensionDelta l E r : ℝ) :
            WithTop ℝ)) ∧
      (∀ n : ℕ, 1 ≤ n →
        (((n : ℝ) * (r : ℝ) -
          (coefficientExtensionRamificationIndex l E : ℝ) *
            (padicValNat l n : ℝ)) : ℝ) ≥
          (r : ℝ) + ((n - 1 : ℕ) : ℝ) * coefficientExtensionDelta l E r) ∧
      (∀ x : E, x ∈ coefficientExtensionDeepIdeal l E r → ∀ n : ℕ, 1 ≤ n →
        coefficientExtensionValuation l E (x ^ n / (Nat.factorial n : E)) ≥
          ((n : ℤ) * (r : ℤ) -
            coefficientExtensionRamificationIndex l E *
              (padicValNat l (Nat.factorial n) : ℤ) : WithTop ℤ)) ∧
      (∀ x : E, x ∈ coefficientExtensionDeepIdeal l E r → ∀ n : ℕ, 1 ≤ n →
        WithTop.map (fun z : ℤ => (z : ℝ))
            (coefficientExtensionValuation l E (x ^ n / (Nat.factorial n : E))) ≥
          ((((n : ℝ) * (r : ℝ) -
            (coefficientExtensionRamificationIndex l E : ℝ) *
              (padicValNat l (Nat.factorial n) : ℝ)) : ℝ) : WithTop ℝ)) ∧
      (∀ x : E, x ∈ coefficientExtensionDeepIdeal l E r → ∀ n : ℕ, 1 ≤ n →
        WithTop.map (fun z : ℤ => (z : ℝ))
            (coefficientExtensionValuation l E (x ^ n / (Nat.factorial n : E))) ≥
          (((r : ℝ) + ((n - 1 : ℕ) : ℝ) * coefficientExtensionDelta l E r : ℝ) :
            WithTop ℝ)) ∧
      (∀ n : ℕ, 1 ≤ n →
        (((n : ℝ) * (r : ℝ) -
          (coefficientExtensionRamificationIndex l E : ℝ) *
            (padicValNat l (Nat.factorial n) : ℝ)) : ℝ) ≥
          (r : ℝ) + ((n - 1 : ℕ) : ℝ) * coefficientExtensionDelta l E r) ∧
      (∀ n : ℕ, 1 ≤ n →
        coefficientExtensionAbsoluteValue l E ((n : E)⁻¹) * (coefficientExtensionQ l E r) ^ n ≤
          (coefficientExtensionQ l E r) * (coefficientExtensionTheta l E r) ^ (n - 1)) ∧
      (∀ n : ℕ, 1 ≤ n →
        coefficientExtensionAbsoluteValue l E ((Nat.factorial n : E)⁻¹) *
            (coefficientExtensionQ l E r) ^ n ≤
          (coefficientExtensionQ l E r) * (coefficientExtensionTheta l E r) ^ (n - 1)) ∧
      (∀ x : E,
        x ∈ coefficientExtensionDeepIdeal l E r ↔
          coefficientExtensionAbsoluteValue l E x ≤ coefficientExtensionQ l E r) ∧
      @TendstoUniformlyOn E E ℕ
        (coefficientExtensionUniformSpace l E)
        (fun (N : ℕ) (x : E) ↦ ∑ n ∈ Finset.range N,
          (-1 : E) ^ n * x ^ (n + 1) / (n + 1 : E))
        (fun x : E ↦ coefficientExtensionTsum l E
          (fun n : ℕ ↦ (-1 : E) ^ n * x ^ (n + 1) / (n + 1 : E)))
        Filter.atTop (coefficientExtensionDeepIdeal l E r) ∧
      @TendstoUniformlyOn E E ℕ
        (coefficientExtensionUniformSpace l E)
        (fun (N : ℕ) (x : E) ↦ ∑ n ∈ Finset.range N, x ^ (n + 1) / (Nat.factorial (n + 1) : E))
        (fun x : E ↦ coefficientExtensionTsum l E
          (fun n : ℕ ↦ x ^ (n + 1) / (Nat.factorial (n + 1) : E)))
        Filter.atTop (coefficientExtensionDeepIdeal l E r) ∧
      (∀ x : E, x ∈ coefficientExtensionDeepIdeal l E r →
        coefficientExtensionTsum l E (fun n : ℕ ↦ (-1 : E) ^ n * x ^ (n + 1) / (n + 1 : E)) ∈
          coefficientExtensionDeepIdeal l E r) ∧
      (∀ x : E, x ∈ coefficientExtensionDeepIdeal l E r →
        coefficientExtensionTsum l E (fun n : ℕ ↦ x ^ (n + 1) / (Nat.factorial (n + 1) : E)) ∈
          coefficientExtensionDeepIdeal l E r) ∧
      @ContinuousOn E E
        (coefficientExtensionTopology l E)
        (coefficientExtensionTopology l E)
        (fun x : E ↦ coefficientExtensionTsum l E
          (fun n : ℕ ↦ (-1 : E) ^ n * x ^ (n + 1) / (n + 1 : E)))
        (coefficientExtensionDeepIdeal l E r) ∧
      @ContinuousOn E E
        (coefficientExtensionTopology l E)
        (coefficientExtensionTopology l E)
        (fun x : E ↦ coefficientExtensionTsum l E
          (fun n : ℕ ↦ x ^ (n + 1) / (Nat.factorial (n + 1) : E)))
        (coefficientExtensionDeepIdeal l E r) ∧
      @TendstoUniformlyOn E E ℕ
        (coefficientExtensionUniformSpace l E)
        (fun (N : ℕ) (x : E) ↦ 1 + ∑ n ∈ Finset.range N,
          x ^ (n + 1) / (Nat.factorial (n + 1) : E))
        (fun x : E ↦ 1 + coefficientExtensionTsum l E
          (fun n : ℕ ↦ x ^ (n + 1) / (Nat.factorial (n + 1) : E)))
        Filter.atTop (coefficientExtensionDeepIdeal l E r) ∧
      @ContinuousOn E E
        (coefficientExtensionTopology l E)
        (coefficientExtensionTopology l E)
        (fun x : E ↦ 1 + coefficientExtensionTsum l E
          (fun n : ℕ ↦ x ^ (n + 1) / (Nat.factorial (n + 1) : E)))
        (coefficientExtensionDeepIdeal l E r) := by
  sorry

end Padic
