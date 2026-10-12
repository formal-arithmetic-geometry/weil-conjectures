/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineGeometricallyIrreducible
public import WeilConjectures.DeligneLaumon.AffineLine.Upper
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The affine-line estimate on an open curve

For a nonempty open `C` of the projective line over `k₀` and a lisse Weil sheaf `F` punctually
pure of weight `w`, the compactly supported cohomology `H_c^r(C, F)` has weights at most `w + r`,
with no ramification condition at infinity (blueprint: `sk-l-dl-general-open-line`). It is the
case `j = 𝟙` of the compact-support upper bound for a middle extension on a smooth geometrically
connected curve (blueprint: `prop-a1-middle-extension-curve-upper`), the middle extension
`(𝟙)_* F` being `F` itself.

## Main statements

- `AlgebraicGeometry.hasWeightsAtMostOver_compactlySupportedCohomology_of_isCurve`: blueprint
  `thm-a1-curve-upper`.
- `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_of_projectiveLine`:
  blueprint `sk-l-dl-general-open-line`.

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

/-- Isomorphic Weil sheaves have isomorphic compactly supported cohomology, with its
Frobenius. -/
theorem WeilSheaf.nonempty_equiv_compactlySupportedCohomology_of_iso {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F G : WeilSheaf k₀ l X} (e : F ≅ G) (r : ℤ) :
    Nonempty ((F.compactlySupportedCohomology r).Equiv (G.compactlySupportedCohomology r)) :=
  ⟨WeilSheaf.globalSectionsEquivOfIso ((WeilComplex.homologySheaf r).mapIso
    ((WeilComplex.derivedLowerShriek k₀ l _).mapIso (WeilSheaf.toComplex.mapIso e)))⟩

/-- **Compact-support upper bound for a middle extension on a curve** (blueprint:
`prop-a1-middle-extension-curve-upper`): let `j : U ⟶ C` be a dense open immersion of smooth
geometrically connected curves over `k₀` and let `F` be a lisse Weil sheaf on `U`, punctually
`ι`-pure of weight `w`. Then `H_c^r(C, j_*F)` has weights at most `w + r` for every `r`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_directImage_of_isCurve
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).HasWeightsAtMostOver
      k₀ ι (w + r) :=
  sorry

/-- **Compact-support upper bound on a curve.** Let `C` be a smooth geometrically connected curve
over `k₀` and let `F` be a lisse Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then every
`H_c^r(C, F)` has weights at most `w + r`: this is
`AlgebraicGeometry.hasWeightsAtMostOver_compactlySupportedCohomology_directImage_of_isCurve` for
the identity of `C`, whose middle extension `(𝟙 C)_* F` is `F` itself
(blueprint: `thm-a1-curve-upper`). -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_of_isCurve {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l C) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w)
    (r : ℤ) :
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have h := hasWeightsAtMostOver_compactlySupportedCohomology_directImage_of_isCurve ι (𝟙 C)
    (by simp) F hF hw r
  obtain ⟨e⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_of_iso
    ((WeilSheaf.lowerStarIdIso k₀ l C).app F) r
  exact FrobeniusModule.HasWeightsAtMost.of_equiv e.symm h

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
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  -- `C` is a smooth geometrically connected curve over `k₀`, being a nonempty open of `ℙ¹_{k₀}`
  have hc := comp_over c (Spec (CommRingCat.of k₀))
  have : GeometricallyIrreducible (C ↘ Spec (CommRingCat.of k₀)) := by
    rw [← hc]
    exact ProjectiveLine.geometricallyIrreducible_of_isOpenImmersion c
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀)) := by
    rw [← hc]
    exact ProjectiveLine.smoothOfRelativeDimension_one_of_isOpenImmersion c
  have : IsSeparated (C ↘ Spec (CommRingCat.of k₀)) := by rw [← hc]; infer_instance
  exact hasWeightsAtMostOver_compactlySupportedCohomology_of_isCurve ι F hF hpure r

end AlgebraicGeometry
