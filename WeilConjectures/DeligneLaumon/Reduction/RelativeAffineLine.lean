/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy
public import WeilConjectures.DeligneLaumon.AffineLine.Upper
public import WeilConjectures.DeligneLaumon.Reduction.RealSheaves
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Weight bounds for direct images from an open of the relative affine line

The two main statements of this file are the geometric input of the Deligne–Laumon reduction
(blueprint section `sec-deligne-laumon-general`):

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
- For `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine`: the projection
  `h : U ⟶ Y` is smooth of relative dimension one with affine fibres
  (`AlgebraicGeometry.AffineSpace.isAffine_fiber_of_isOpenImmersion`), so the relative-curve step
  `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber` applies. That
  step follows Kiehl–Weissauer I.7: compact-support base change and the curve estimate give the
  punctual bound on every fibre; the direct images of the real envelope `F⁰ ⊕ (F⁰)^∨` have
  reduced local `L`-fractions with real numerator and denominator, so they are `ι`-real and
  `AlgebraicGeometry.WeilSheaf.IsReal.isMixed` applies; the direct image of `F` is a twisted
  direct summand, hence mixed, and the punctual bound cuts its weights down to `w + r`.

## Main statements

- `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_of_projectiveLine`:
  blueprint `sk-l-dl-general-open-line`.
- `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine`:
  blueprint `lem-zl-affine-curve-hc2-purity`, stated in
  `WeilConjectures.WeilSheaf.CurveTopCohomology`.
- `AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber`: blueprint
  `lem-zl-relative-curve-punctual`.
- `AlgebraicGeometry.isReal_higherLowerShriek_of_isAffine_fiber`: blueprint
  `lem-zl-relative-envelope-factor-reality`.
- `AlgebraicGeometry.exists_isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber`:
  blueprint `lem-zl-relative-curve-mixedness`.
- `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber`: blueprint
  `thm-zl-relative-affine-curve-core`.
- `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine`: blueprint
  `sk-p-dl-general-relative-line`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §3.
- [Kiehl, Weissauer, *Weil conjectures, perverse sheaves and l-adic Fourier
  transform*][kiehlWeissauer2001], Springer (2001), I.7.
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
    [c.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l C) (hF : F.IsLisse) (w : ℝ) (hpure : F.IsPunctuallyPureOfWeight ι w)
    (r : ℤ) :
    -- `C ↘ Spec k₀` is separated and locally of finite type, being `c` followed by `ℙ¹ ↘ Spec k₀`
    haveI : IsSeparated (C ↘ Spec (CommRingCat.of k₀)) := by rw [← comp_over c]; infer_instance
    haveI : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over c]; infer_instance
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) :=
  sorry

section RelativeCurve

/-! ### Relative affine curves

Throughout, `h : U ⟶ Y` is a smooth separated morphism of relative dimension one between
`k₀`-schemes of finite type, `Y` separated, whose fibres `h.fiber y` are affine: every nonempty
geometric fibre of `h` is a smooth affine curve. -/

variable {U Y : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (h : U ⟶ Y)
  [h.IsOver (Spec (CommRingCat.of k₀))] [SmoothOfRelativeDimension 1 h] [IsSeparated h]
  [QuasiCompact h]

/-- **Punctual upper bound in a relative affine curve.** Let `h : U ⟶ Y` be a smooth separated
morphism of relative dimension one with affine fibres, and let `F` be a lisse Weil sheaf on `U`,
punctually `ι`-pure of weight `w`. Then `Rⁱh₀!F` has weights at most `w + i`: by compactly
supported base change its stalk at a closed point `y` is `H_c^i(U_ȳ, F)`, the restriction of
`F` to the fibre is pure of weight `w` relative to `κ(y)`
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.upperStar`), and the curve estimate
applies to each geometric component of the affine fibre
(blueprint: `lem-zl-relative-curve-punctual`). -/
theorem hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber
    (hfib : ∀ y, IsAffine (h.fiber y)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ((WeilSheaf.higherLowerShriek k₀ l h i).obj F).HasWeightsAtMost ι (w + i) :=
  -- TODO(adic): needs compactly supported base change for Weil sheaves and the curve estimate
  -- over the residue fields of `Y`
  sorry

/-- **Reality of the relative factors of an envelope.** Let `h : U ⟶ Y` be as in
`AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber` and let `E` be a lisse
`ι`-real Weil sheaf on `U`, punctually `ι`-pure of weight `0`. Then every `Rⁱh₀!E` is `ι`-real.
At a closed point `y` the trace formula writes the `L`-function of the fibre as `P₁ / P₂`, with
real coefficients since `E` is real; the reciprocal roots of `P₁` have modulus at most
`q_y ^ (1 / 2)` and those of `P₂` modulus `q_y`
(`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine`), so the
fraction is reduced (`Polynomial.isCoprime_of_norm_inv_roots`) and both factors are real
(`Polynomial.map_conj_eq_self_of_isCoprime`)
(blueprint: `lem-zl-relative-envelope-factor-reality`). -/
theorem isReal_higherLowerShriek_of_isAffine_fiber (hfib : ∀ y, IsAffine (h.fiber y))
    (E : WeilSheaf k₀ l U) (hE : E.IsLisse) (hreal : E.IsReal ι)
    (hpure : E.IsPunctuallyPureOfWeight ι 0) (i : ℕ) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ((WeilSheaf.higherLowerShriek k₀ l h i).obj E).IsReal ι :=
  -- TODO(adic): needs compactly supported base change and the trace formula on the fibres
  sorry

/-- **Mixedness of the direct images over a relative affine curve.** Let `h : U ⟶ Y` be as in
`AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber` and let `F` be a lisse
Weil sheaf on `U`, punctually `ι`-pure of weight `w`. Then each `Rⁱh₀!F` is `ι`-mixed of
weights at most some `v`. The direct images of the real envelope `E = F⁰ ⊕ (F⁰)^∨` of `F` are
real (`AlgebraicGeometry.isReal_higherLowerShriek_of_isAffine_fiber`), hence mixed
(`AlgebraicGeometry.WeilSheaf.IsReal.isMixed`); `Rⁱh₀!F⁰` is a direct summand of `Rⁱh₀!E`, and
`Rⁱh₀!F` is its constant twist back by the projection formula
(blueprint: `lem-zl-relative-curve-mixedness`). -/
theorem exists_isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber
    (hfib : ∀ y, IsAffine (h.fiber y)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ∃ v : ℝ, ((WeilSheaf.higherLowerShriek k₀ l h i).obj F).IsMixedOfWeightsAtMost ι v := by
  have := SmoothOfRelativeDimension.smooth 1 h
  obtain ⟨w', b, hw', hb⟩ := hw.exists_units_norm_eq ι
  let R := WeilSheaf.higherLowerShriek k₀ l h i
  -- the direct images of the real envelope are real, hence mixed
  obtain ⟨v, hv⟩ := (isReal_higherLowerShriek_of_isAffine_fiber ι h hfib (F.realEnvelope hF b)
    (hF.realEnvelope b) (WeilSheaf.isReal_realEnvelope hF hw' hb) (hw'.realEnvelope hF hb)
    i).isMixed
  -- `Rⁱh₀!(F ⊗ 𝓑_b)` is a direct summand of `Rⁱh₀!E`
  have h₀ : (R.obj (F.constantTwist b)).IsMixedOfWeightsAtMost ι v :=
    hv.of_mono (R.map (Limits.biprod.inl : F.constantTwist b ⟶ F.realEnvelope hF b))
  obtain ⟨e⟩ := WeilSheaf.nonempty_higherLowerShriek_constantTwist_iso h F b i
  exact ⟨_, ((h₀.of_iso e).constantTwist (b := b⁻¹) rfl).of_iso
    ((R.obj F).constantTwistInvIso b)⟩

/-- **Pure lisse relative affine-curve step.** Let `h : U ⟶ Y` be a smooth separated morphism of
relative dimension one between separated `k₀`-schemes of finite type whose fibres are affine,
so that every nonempty geometric fibre is a smooth affine curve, and let `F` be a lisse Weil
sheaf on `U`, punctually `ι`-pure of weight `w`. Then `Rⁱh₀!F` is `ι`-mixed of weights at most
`w + i`: it is mixed
(`AlgebraicGeometry.exists_isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber`), its
local Frobenius eigenvalues have weights at most `w + i`
(`AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber`), and the punctual
bound cuts the mixed filtration down
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_hasWeightsAtMost`)
(blueprint: `thm-zl-relative-affine-curve-core`). -/
theorem isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber
    (hfib : ∀ y, IsAffine (h.fiber y)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ((WeilSheaf.higherLowerShriek k₀ l h i).obj F).IsMixedOfWeightsAtMost ι (w + i) := by
  have := SmoothOfRelativeDimension.smooth 1 h
  obtain ⟨v, hv⟩ :=
    exists_isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber ι h hfib F hF hw i
  exact hv.of_hasWeightsAtMost
    (hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber ι h hfib F hF hw i)

end RelativeCurve

-- the surjectivity of `h` is not needed: an empty fibre contributes nothing
set_option linter.unusedVariables false in
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
      F).IsMixedOfWeightsAtMost ι (w + r) := by
  -- `h = u ≫ 𝔸¹_Y ↘ Y` is smooth of relative dimension `0 + 1` with affine fibres
  have : SmoothOfRelativeDimension 1 (u ≫ 𝔸(PUnit.{u + 1}; Y) ↘ Y) := by
    rw [show 1 = 0 + Nat.card PUnit.{u + 1} by simp]
    infer_instance
  exact isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber ι _
    (AffineSpace.isAffine_fiber_of_isOpenImmersion u) F hF hpure r

end AlgebraicGeometry
