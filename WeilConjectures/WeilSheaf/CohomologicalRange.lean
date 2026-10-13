/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Cohomology

/-!
# The cohomological range of a curve

The compactly supported cohomology `H_c^r(X ⊗ k̄, G)` of a Weil sheaf `G` on a separated
`k₀`-scheme `X` of finite type and of dimension at most one is concentrated in degrees
`0, 1, 2`. In particular this holds on a smooth affine curve.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_krullDim_le_one`:
  the curve clause of the Euler-product form of the trace formula, stated with `sorry`.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine`: the
  compactly supported cohomology of a smooth affine curve is concentrated in degrees `0, 1, 2`.

## Implementation notes

The blueprint proves the range of a smooth affine curve at the finite coefficient levels
`𝒪_E / ϖⁿ`, by the cohomological dimension of a proper curve and a Mittag-Leffler argument for
the passage to the limit. Weil sheaves in the repository have coefficients `ℚ̄_ℓ` directly and no
finite coefficient levels, so this argument cannot be run. The `ℚ̄_ℓ`-statement it produces is
clause (3) of the Euler-product form of the trace formula (blueprint
`thm-trf-l-function-euler-product`), for a sheaf placed in degree zero on a scheme of dimension
at most one; it is stated here for Weil sheaves, without the finite-level hypotheses (étale-origin
witnesses and compactification admissibility of the reductions of a lattice) of the blueprint,
which have no counterpart for `ℚ̄_ℓ`-Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `thm-trf-l-function-euler-product`, clause (3): if the separated `k₀`-scheme `X` of
finite type has dimension at most one and `G` is a Weil sheaf on `X`, placed in degree zero, then
`H_c^r(X ⊗ k̄, G) = 0` for `r ∉ {0, 1, 2}`, so that the Euler product of the trace formula only
involves `H_c^0`, `H_c^1` and `H_c^2`. -/
theorem subsingleton_compactlySupportedCohomology_of_krullDim_le_one
    (hX : topologicalKrullDim X ≤ 1) (G : WeilSheaf k₀ l X) {r : ℤ} (hr : r < 0 ∨ 2 < r) :
    Subsingleton (G.compactlySupportedCohomology r).carrier :=
  sorry

/-- *Cohomological range of an affine curve.* If `X` is a smooth affine curve over `k₀` and `G`
is a constructible Weil sheaf on `X`, then `H_c^r(X ⊗ k̄, G) = 0` for `r ∉ {0, 1, 2}`: a smooth
curve has dimension at most one, and the compactly supported cohomology of a sheaf on a scheme of
dimension at most one is concentrated in degrees `0, 1, 2`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_krullDim_le_one`).
(blueprint: `lem-zl-affine-curve-range`) -/
theorem subsingleton_compactlySupportedCohomology_of_isAffine [IsAffine X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton (G.compactlySupportedCohomology r).carrier :=
  subsingleton_compactlySupportedCohomology_of_krullDim_le_one
    (by exact_mod_cast
      topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (CommRingCat.of k₀)) 1) G hr

end WeilSheaf

end AlgebraicGeometry
