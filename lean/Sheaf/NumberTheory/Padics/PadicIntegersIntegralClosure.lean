/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Integers in a finite extension of p-adic fields

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-prop-sfb-cartesian-coefficients/sk-prop-sfb-cartesian-coefficients-finite-free.proof.md,
first sentence (blueprint: lem-sfb-padic-integers-integral-closure).
-/

@[expose] public section

universe u v

namespace Padic

/-- For finite p-adic extensions `E ⊆ F`, the unit ball in `F` is the
integral closure of the unit ball in `E`.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-prop-sfb-cartesian-coefficients/sk-prop-sfb-cartesian-coefficients-finite-free.proof.md,
first sentence (blueprint: lem-sfb-padic-integers-integral-closure).
Proof:
1. Put `K = ℚ_[l]` and `A = ℤ_[l]` (def-weil-l-adic-numbers). Its norm is complete
   and nontrivial since `|l| = l⁻¹ < 1`. The extending absolute value is
   nonarchimedean by lem-weil-l-adic-extension-absolute-value. Choose a finite
   `K`-basis `bᵢ` of `F`. The coordinate equivalence `F ≃ₗ[K] Kᵈ` is continuous
   by lem-weil-pbc-finite-dimensional-linear-homeomorphism: both spaces are
   Hausdorff topological vector spaces, using compatibility with the base norm.
2. Continuity gives `ε > 0` such that `|y| < ε` forces every coordinate `cᵢ(y)`
   to have absolute value less than one. Choose `N ≥ 0` with `l⁻ᴺ < ε`.
   For `|x| ≤ 1` and every `n ≥ 0`, including zero, `|lᴺ xⁿ| ≤ l⁻ᴺ < ε`.
   Thus `lᴺ cᵢ(xⁿ)` belongs to `A` and
   `xⁿ = ∑ i, (lᴺ cᵢ(xⁿ)) (l⁻ᴺ bᵢ)` lies in the finite `A`-module
   `L = ∑ i, A (l⁻ᴺ bᵢ)`.
3. The DVR `A` is a PID (def-sc-discrete-valuation-ring), hence Noetherian by
   lem-weil-pbc-pid-noetherian-normal. The algebra `A[x]`, consisting of finite
   sums of powers of `x`, is an `A`-submodule of `L`. It is finite over `A` by
   lem-weil-pbc-noetherian-submodule-finite.
4. By lem-weil-pbc-finite-algebra-is-integral, `x` satisfies a monic polynomial
   over `A`. Compatibility of absolute values embeds `A` in the integer ring of
   `E`, and mapping the polynomial's coefficients preserves monicity and its
   vanishing in `F`. This proves integrality over the smaller integer ring,
   as defined by def-weil-pbc-integral-closure.
5. Conversely, a monic equation of degree `r ≥ 1` gives
   `xʳ = -∑ j < r, aⱼ xʲ`, with `|aⱼ| ≤ 1` by compatibility of the extending
   absolute values (def-weil-l-adic-coefficient-extension). If `t = |x| > 1`,
   the ultrametric inequality gives `t^r ≤ t^(r-1) < t^r`, a contradiction.
   Hence `|x| ≤ 1`. The two implications give the pointwise equivalence and
   therefore identify the larger integer ring with the integral closure.
-/
theorem padic_integers_integralClosure
    (l : ℕ) [Fact l.Prime]
    (E : Type u) (F : Type v) [Field E] [Field F]
    [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) (x : F) :
    x ∈ coefficientExtensionIntegers l F ↔
      x ∈ @integralClosure (coefficientExtensionIntegers l E) F _ _
        ((i.toRingHom.comp (coefficientExtensionIntegers l E).subtype).toAlgebra) := by
  sorry

end Padic
