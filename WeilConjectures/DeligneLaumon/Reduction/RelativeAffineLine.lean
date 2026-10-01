/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.DeligneLaumon.AffineLine.Upper
public import WeilConjectures.DeligneLaumon.Reduction.Weights

/-!
# Weight bounds for direct images from an open of the relative affine line

The two statements of this file are the geometric input of the Deligne–Laumon reduction (blueprint
section `sec-deligne-laumon-general`):

- for a nonempty open `C` of the projective line over `k₀` and a lisse Weil sheaf `F` punctually
  pure of weight `w`, the compactly supported cohomology `H_c^r(C, F)` has weights at most
  `w + r`, with no ramification condition at infinity;
- for the projection `h : U ⟶ Y` of an open `U` of the relative affine line `𝔸¹_Y` with surjective
  projection, and `F` lisse and punctually pure of weight `w`, the sheaf `Rʳh₀!F` is mixed of
  weights at most `w + r`.

The first statement is a *punctual* upper bound on Frobenius eigenvalues
(`FrobeniusModule.HasWeightsAtMostOver`), not mixedness; the second upgrades it to mixedness, and
the reality argument it runs is exactly what that upgrade costs.

## Conventions

We use the relative affine space `AlgebraicGeometry.AffineSpace` of mathlib and the relative
projective space `AlgebraicGeometry.ProjectiveSpace` of this repository, whose index types record
the coordinates: `𝔸(PUnit; Y)` is the relative affine line — the same spelling as
`AlgebraicGeometry.affineLine` — and `ℙ(ULift (Fin 2); S)` the relative projective line.

## Implementation notes

- For `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_of_projectiveLine`: move
  a rational point of `C` to infinity by an automorphism of `ℙ¹`, so that the ordinary middle
  extension of `F` to the new affine line is unramified at the new infinity and the affine-line
  estimate `hasWeightsAtMost_compactlySupportedCohomology_directImage` of
  `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen` applies; then compare `j₀!F` with `j₀*F` through
  their finite-support quotient.
- For `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine`: compact-support
  base change and the previous statement give the punctual bound on every geometric fibre;
  mixedness comes from adding the dual twist `F ∨ ⊗ T_w` to `F`, whose local `L`-function is a
  reduced fraction with real numerator and denominator, so that `Rʳh₀!` of the sum is `ι`-real and
  `AlgebraicGeometry.WeilSheaf.IsReal.isMixed` applies.

## Main statements

- `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_of_projectiveLine`:
  blueprint `sk-l-dl-general-open-line`.
- `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine`: blueprint
  `sk-p-dl-general-relative-line`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §3.
- [Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*][laumon1987], Publ. Math. IHÉS **65** (1987).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (ι : PadicAlgCl l →+* ℂ)

/-- Let `C` be a nonempty open subscheme of the projective line `ℙ¹_{k₀}` and let `F` be a lisse
Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then the compactly supported cohomology
`H_c^r(C, F)` of the structure morphism

```
C --- c ---> ℙ¹_{k₀}
  \            |
   \           | ↘
    `--------> Spec k₀
```

has weights at most `w + r`, with no ramification restriction at the point at infinity
(blueprint: `sk-l-dl-general-open-line`). -/
theorem hasWeightsAtMost_compactlySupportedCohomology_of_projectiveLine {C : Scheme.{u}}
    [Nonempty C] [C.Over (Spec (CommRingCat.of k₀))]
    (c : C ⟶ ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k₀))) [IsOpenImmersion c]
    [c.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l C) (hF : F.IsLisse) (w : ℝ)
    (hpure : F.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) :=
  sorry

/-- Let `Y` be a separated `k₀`-scheme of finite type, let `U` be an open subscheme of the relative
affine line `𝔸¹_Y` whose projection `h` to `Y` is surjective, and let `F` be a lisse Weil sheaf on
`U`, punctually `ι`-pure of weight `w`. Then `Rʳh₀!F` is mixed of weights at most `w + r`:

```
U --- u ---> 𝔸¹_Y
  \            |
   \ h         | ↘
    `--------> Y
```

(blueprint: `sk-p-dl-general-relative-line`). -/
theorem isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine {U Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (u : U ⟶ 𝔸(PUnit.{u + 1}; Y))
    [IsOpenImmersion u] [QuasiCompact u] [u.IsOver (Spec (CommRingCat.of k₀))]
    (hu : Surjective (u ≫ 𝔸(PUnit.{u + 1}; Y) ↘ Y)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse)
    (w : ℝ) (hpure : F.IsPunctuallyPureOfWeight ι w) (r : ℕ) :
    ((WeilSheaf.higherLowerShriek k₀ l (u ≫ 𝔸(PUnit.{u + 1}; Y) ↘ Y) r).obj
      F).IsMixedOfWeightsAtMost ι (w + r) :=
  sorry

end AlgebraicGeometry
