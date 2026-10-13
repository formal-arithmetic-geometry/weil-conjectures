/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.TraceIsomorphism

/-!
# Cohomology of the affine line with constant coefficients

The geometric affine line `𝔸¹_k̄` has the cohomology of a point: `H⁰(𝔸¹, ℚ̄_ℓ) = ℚ̄_ℓ` and
`Hʳ(𝔸¹, ℚ̄_ℓ) = 0` for `r ≠ 0`. By Poincaré duality on the smooth curve `𝔸¹`, the compactly
supported cohomology `H_cʳ(𝔸¹, ℚ̄_ℓ)`, dual to `H^{2-r}(𝔸¹, ℚ̄_ℓ(1))`, vanishes for `r ≠ 2`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_affineLine`: the vanishing
  of `Hʳ(𝔸¹, ℚ̄_ℓ)` for `r ≠ 0`, stated with `sorry`.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant_affineLine`:
  the vanishing of `H_cʳ(𝔸¹, ℚ̄_ℓ)` for `r ≠ 2`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.WeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Constant cohomology of the affine line.** `Hʳ(𝔸¹_k̄, ℚ̄_ℓ) = 0` for `r ≠ 0`: the affine
line is connected, of cohomological dimension one, and `H¹(𝔸¹_k̄, ℤ/n) ≅ Pic(𝔸¹_k̄)[n] = 0`.
(blueprint: `lem-fd-affine-line-constant-cohomology`, subsection `sk-lem-as-properties`) -/
theorem subsingleton_cohomology_adicConstant_affineLine {r : ℤ} (hr : r ≠ 0) :
    Subsingleton ((adicConstant k₀ l (affineLine k₀)).cohomology r).carrier :=
  sorry

/-- `H_cʳ(𝔸¹_k̄, ℚ̄_ℓ) = 0` for `r ≠ 2`: by Poincaré duality on the smooth curve `𝔸¹`, it is dual
to `H^{2-r}(𝔸¹_k̄, ℚ̄_ℓ(1))`, which is `H^{2-r}(𝔸¹_k̄, ℚ̄_ℓ)` up to the Frobenius, and vanishes
since `2 - r ≠ 0`. -/
theorem subsingleton_compactlySupportedCohomology_adicConstant_affineLine {r : ℤ}
    (hr : r ≠ 2) :
    Subsingleton ((adicConstant k₀ l (affineLine k₀)).compactlySupportedCohomology r).carrier := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  obtain ⟨P, hP, -⟩ := exists_isPerfPair_compactlySupportedCohomology_adicConstant k₀ l
    (affineLine k₀) 1 r (2 - r) (by push_cast; ring)
  obtain ⟨E⟩ := nonempty_equiv_cohomology_tateTwistSheaf k₀ l (affineLine k₀) ((1 : ℕ) : ℤ)
    (2 - r)
  have : Subsingleton (((adicConstant k₀ l (affineLine k₀)).cohomology (2 - r)).tateTwist
      (Nat.card k₀) ((1 : ℕ) : ℤ)).carrier :=
    subsingleton_cohomology_adicConstant_affineLine k₀ l (r := 2 - r) (by omega)
  have : Subsingleton ((tateTwistSheaf k₀ l (affineLine k₀) ((1 : ℕ) : ℤ)).cohomology
      (2 - r)).carrier :=
    E.toLinearEquiv.toEquiv.subsingleton
  exact hP.bijective_left.injective.subsingleton

end AlgebraicGeometry.WeilSheaf
