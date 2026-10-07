/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.DeligneLaumon.AffineLine.Defs

/-!
# Exactness of the ordinary direct image at a fixed pure weight

The ordinary direct image `j_*` along a dense open immersion of smooth curves is only left
exact in general. The obstruction to surjectivity on the right is the connecting map
`δ : j_*F₂ → R¹j_*F₁`, which vanishes on the open. At a missing point the source has weights at
most `w` by semicontinuity, while local boundary duality
(`AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage`) identifies `(R¹j_*F₁)_s̄`
with the dual of the middle-extension stalk of `F₁^∨`, twisted by `(-1)`, whose weights are
therefore at least `w + 2`. A Frobenius-equivariant map across this strict weight gap is zero,
so `δ` vanishes on every geometric stalk and `j_*` is exact on short exact sequences of lisse
sheaves of one and the same pure weight.

Purity of the middle term is not assumed: the spectrum of the middle stalk is the union of the
spectra of the outer two, so it follows from purity of `F₁` and `F₃`.

## Main statements

- `AlgebraicGeometry.shortExact_map_directImage`: exactness of `j_*` at a fixed pure weight.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/--
For a short exact sequence `0 → F₁ → F → F₂ → 0` of lisse Weil sheaves on a dense open `U₀` of
a smooth curve, with `F₁` and `F₂` punctually `ι`-pure of one and the same weight `w`, the
ordinary direct images form a short exact sequence on the curve:

```
  0 ──▶ F₁ ──▶ F ──▶ F₂ ──▶ 0        on U₀
        │      │      │
     j_*│   j_*│   j_*│
        ▼      ▼      ▼
  0 ▶ j_*F₁ ▶ j_*F ▶ j_*F₂ ▶ 0        on X
```
(blueprint: `sk-p-dl-a1-exact`)
-/
theorem shortExact_map_directImage (ι : PadicAlgCl l →+* ℂ)
    {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsDominant j]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (S : ShortComplex (WeilSheaf k₀ l U)) (hS : S.ShortExact)
    (h₁ : S.X₁.IsLisse) (h₂ : S.X₂.IsLisse) (h₃ : S.X₃.IsLisse) {w : ℝ}
    (p₁ : S.X₁.IsPunctuallyPureOfWeight ι w)
    (p₃ : S.X₃.IsPunctuallyPureOfWeight ι w) :
    (S.map (WeilSheaf.directImage j)).ShortExact := by
  sorry

end AlgebraicGeometry
