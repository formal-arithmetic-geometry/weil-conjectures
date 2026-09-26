/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.DegreeOne
public import WeilConjectures.DeligneLaumon.AffineLine.Endpoints
public import WeilConjectures.DeligneLaumon.AffineLine.Exactness

/-!
# The Deligne–Laumon estimate on the affine line

Let `j : U₀ ↪ 𝔸¹_{𝔽_q}` be a dense open immersion and `F` a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^r(𝔸¹, j_*F)` has
weights at most `w + r` for every `r`.

The endpoint lemma `AlgebraicGeometry.compactlySupportedCohomology_directImage_endpoints`
settles every degree except one: degree zero vanishes and degree two is pure of weight
`w + 2`. For degree one, choose a finite composition filtration of the Weil representation of
`F`; its lisse irreducible factors are still pure of weight `w`, their stalk spectra being
subquotient spectra, and still unramified at infinity. A geometrically constant factor extends
constantly to the whole line and has `H_c^1 = 0` because `RΓ_c(𝔸¹, ℚ̄_ℓ) = ℚ̄_ℓ(-1)[-2]`;
every other factor is covered by
`AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one`. Each filtration step
stays short exact after `j_*` by `AlgebraicGeometry.shortExact_map_directImage`, so the long
exact sequence gives an exact triple in degree one whose middle term inherits the common upper
bound, characteristic polynomials being multiplicative in short exact sequences of Frobenius
modules. Induction through the filtration finishes the proof; no splitting of the filtration
and no semisimplicity theorem for pure sheaves is used.

## Main statements

- `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_directImage`: the
  affine-line estimate, with the two sharper endpoint assertions.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

/-- Blueprint `sk-thm-dl-a1-upper`: Deligne–Laumon affine-line estimate. Let
`j : U₀ ↪ 𝔸¹_{k₀}` be a dense open immersion and let `F` be a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^r(𝔸¹, j_*F)` has
weights at most `w + r` for every integer `r`; more precisely degree zero vanishes and degree
two is pure of weight `w + 2`, so only the degree-one bound needs the Fourier argument. -/
theorem hasWeightsAtMost_compactlySupportedCohomology_directImage (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) (hinf : WeilSheaf.IsUnramifiedAtInfinity D.j D.sheaf)
    {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (∀ r : ℤ, (D.directImage.compactlySupportedCohomology r).HasWeightsAtMost ι (Nat.card k₀)
        (w + r)) ∧
      Subsingleton (D.directImage.compactlySupportedCohomology 0).carrier ∧
      (D.directImage.compactlySupportedCohomology 2).IsPureOfWeight ι (Nat.card k₀)
        (w + 2) := by
  sorry

end AlgebraicGeometry
