/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineIrreducible
public import WeilConjectures.DeligneLaumon.AffineLine.DegreeOne
public import WeilConjectures.DeligneLaumon.AffineLine.DenseOpen
public import WeilConjectures.DeligneLaumon.AffineLine.Endpoints
public import WeilConjectures.DeligneLaumon.AffineLine.Exactness
public import WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents
public import WeilConjectures.DeligneLaumon.AffineLine.UpperReduction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The Deligne–Laumon estimate on the affine line

Let `j : U₀ ↪ 𝔸¹_{𝔽_q}` be a dense open immersion and `F` a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^r(𝔸¹, j_*F)` has
weights at most `w + r` for every `r`.

The endpoint lemmas of `WeilConjectures.DeligneLaumon.AffineLine.Endpoints` settle every degree
except one: degree zero vanishes and degree two is pure of weight `w + 2`. For degree one,
choose a finite composition filtration of the Weil representation of `F`; its lisse irreducible
factors are still pure of weight `w`, their stalk spectra being subquotient spectra, and still
unramified at infinity. A geometrically constant factor extends constantly to the whole line
and has `H_c^1 = 0` because `RΓ_c(𝔸¹, ℚ̄_ℓ) = ℚ̄_ℓ(-1)[-2]`; every other factor is covered by
`AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one`. Each filtration step
stays short exact after `j_*` by `AlgebraicGeometry.shortExact_map_directImage`, so the long
exact sequence gives an exact triple in degree one whose middle term inherits the common upper
bound, characteristic polynomials being multiplicative in short exact sequences of Frobenius
modules. Induction through the filtration finishes the proof.

The blueprint proof opens with two further steps: a base change to a finite constant extension
`𝔽_{q^m}` and a reduction to geometrically irreducible graded pieces. They are not needed here,
and no statement of this block corresponds to them: the Fourier route of
`sk-p-dl-a1-middle` only assumes arithmetic irreducibility, so the composition filtration of
the Weil representation over `k₀` is already fine enough, and neither the filtration nor a
semisimplicity theorem for pure sheaves is used.

## Main statements

In the namespace `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen`:

- `hasWeightsAtMost_compactlySupportedCohomology_directImage`: the affine-line estimate.
- `subsingleton_compactlySupportedCohomology_directImage_zero` and
  `isPureOfWeightOver_compactlySupportedCohomology_directImage_two`: the two sharper endpoint
  assertions on the line.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Let `j : U₀ ↪ 𝔸¹_{k₀}` be a dense open immersion and let `F` be a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^r(𝔸¹, j_*F)` has
weights at most `w + r` for every integer `r`. (blueprint: `sk-thm-dl-a1-upper`) -/
theorem hasWeightsAtMost_compactlySupportedCohomology_directImage (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) (hinf : D.IsUnramifiedAtInfinity) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    (D.directImage.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  sorry

/-- In degree zero the compactly supported cohomology of `j_*F` on the line vanishes.
(blueprint: `sk-thm-dl-a1-upper`) -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero
    (D : LisseOnDenseOpen k₀ l) :
    Subsingleton (D.directImage.compactlySupportedCohomology 0).carrier := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  exact AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero D.j D.sheaf
    D.lisse

/-- In degree two the compactly supported cohomology of `j_*F` on the line is pure of weight
`w + 2`, not merely of weights at most `w + 2`. (blueprint: `sk-thm-dl-a1-upper`) -/
theorem isPureOfWeightOver_compactlySupportedCohomology_directImage_two
    (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  exact AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two D.j
    D.sheaf ι D.lisse hw

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
