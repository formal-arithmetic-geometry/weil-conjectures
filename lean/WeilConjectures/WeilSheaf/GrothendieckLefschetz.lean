/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The Grothendieck–Lefschetz trace formula for Weil sheaves

For a separated `k₀`-scheme `X` of finite type and a Weil sheaf `F` on `X`, the alternating sum of
the traces of the `m`-th power of the geometric Frobenius on the compactly supported cohomology
`H_c^i(X ⊗ k̄, F)` is the sum, over the `𝔽_{qᵐ}`-points `y` of `X`, of the traces of the local
Frobenius `F_{y, m}` on the geometric stalks: grouping the `𝔽_{qᵐ}`-points by the closed point
`x` of `X` they lie over, a closed point of degree `e ∣ m` carries `e` such points, each with
local Frobenius `F_x^{m / e}`. This is blueprint `thm-trf-grothendieck-lefschetz-qbar` of the
trace formula chapter, in the case of a Weil sheaf in degree zero; it is stated here with
`sorry`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The Grothendieck–Lefschetz trace formula** (blueprint:
`thm-trf-grothendieck-lefschetz-qbar`, for a Weil sheaf placed in degree zero): for every
`m ≥ 1`,

`∑ᵢ (-1)ⁱ tr (Fᵐ ∣ H_c^i(X ⊗ k̄, F)) = ∑_{y ∈ X(𝔽_{qᵐ})} tr (F_{y, m} ∣ F_ȳ)
  = ∑_{x closed, deg x ∣ m} deg x · tr (F_x^{m / deg x} ∣ F_x̄)`. -/
theorem sum_trace_compactlySupportedCohomology (F : WeilSheaf k₀ l X) {m : ℕ} (hm : m ≠ 0) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l)
        (F.compactlySupportedCohomology i).carrier
        ((F.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ x : X.finitePoints, if (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ m then
        ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : PadicAlgCl l) *
          LinearMap.trace (PadicAlgCl l) (F.stalk x).carrier ((F.stalk x).frobeniusEnd ^
            (m / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))
      else 0 :=
  sorry

end AlgebraicGeometry.WeilSheaf
