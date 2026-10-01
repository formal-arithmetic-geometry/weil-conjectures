/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherNormalization
public import WeilConjectures.DeligneLaumon.Reduction.FormalSteps
public import WeilConjectures.DeligneLaumon.Reduction.RealSheaves
public import WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine

/-!
# The Deligne–Laumon direct-image bound

This file states the two main results of the blueprint section `sec-deligne-laumon-general`: for a
separated finite-type morphism `f : X ⟶ Y` of schemes of finite type over `k₀ = 𝔽_q` and a
constructible Weil sheaf `F` mixed of weights at most `w`, the sheaf `Rʳf₀!F` is mixed of weights
at most `w + r` for every `r`; and the derived form, that `Rf₀!K` is mixed of weights at most `w`
whenever the bounded constructible Weil complex `K` is.

## Implementation notes

- For `AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`: Noetherian induction and
  finite affine stratifications reduce a general `f` to a dominant affine morphism of integral
  schemes, which factors generically through a finite morphism to an iterated relative affine line
  (`AlgebraicGeometry.exists_dense_isFinite_toIteratedAffineLine`); the quasi-finite and
  composition lemmas of `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` and the relative
  affine-line proposition
  `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine` then apply, and
  open–closed reduction restores the discarded strata.
- For `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek`: the finite
  hypercohomology spectral sequence `Rᵃf₀!𝓗ᵇ(K) ⇒ 𝓗ᵃ⁺ᵇ(Rf₀!K)`, whose left-hand term is mixed of
  weights at most `w + a + b` by the theorem above.

## Main statements

- `AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`: blueprint
  `sk-thm-dl-general-sheaf`.
- `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek`: blueprint
  `sk-cor-dl-general-complex`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), Théorème
  3.3.1.
- [Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*][laumon1987], Publ. Math. IHÉS **65** (1987).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- The hypotheses that the base `Y` is separated of finite type over `k₀` do not occur in the two
-- statements below, so they are spelled out rather than taken from a `variable` block, which would
-- not include them.
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- For a separated finite-type morphism `f : X ⟶ Y` of schemes of finite type over `k₀ = 𝔽_q` and
a constructible Weil sheaf `F` on `X` mixed of weights at most `w`, the sheaf `Rʳf₀!F` is mixed of
weights at most `w + r`, for every `r` (blueprint: `sk-thm-dl-general-sheaf`). -/
theorem hasDirectImageWeightBound_over_finiteField (ι : PadicAlgCl l →+* ℂ) (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] : HasDirectImageWeightBound k₀ ι f :=
  sorry

/-- If `K` is a bounded constructible Weil complex on `X` mixed of weights at most `w`, then
`Rf₀!K` is mixed of weights at most `w` (blueprint: `sk-cor-dl-general-complex`). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    {K : WeilComplex k₀ l X} (hK : K.IsMixedOfWeightsAtMost ι w) (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    ((WeilComplex.derivedLowerShriek k₀ l f).obj K).IsMixedOfWeightsAtMost ι w :=
  sorry

end AlgebraicGeometry
