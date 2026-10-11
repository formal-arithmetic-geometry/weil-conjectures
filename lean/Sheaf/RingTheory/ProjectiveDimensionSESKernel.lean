module

public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Ring

/-! # Projective dimension in a short exact sequence

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 065S, part (1)
(blueprint: lem-weil-pbc-projective-dimension-ses-kernel).
-/

/-- In a short exact sequence `0 → M' → M → M'' → 0` of `R`-modules, if `M` has a
projective resolution of length at most `m` and `M''` one of length at most `m + 1`,
then `M'` has a projective resolution of length at most `m`. Source: Stacks Project,
Algebra, Lemma Tag 065S, part (1)
(blueprint: lem-weil-pbc-projective-dimension-ses-kernel).

Proof: fix an arbitrary module `N` and set `i = m + 1` (so `i ≥ 1`). By
`lem-weil-pbc-projective-dimension-ext-characterization` (065R) the resolution of `M`
gives `Ext^i(M, N) = 0` and the resolution of `M''` gives `Ext^(i+1)(M'', N) = 0`.
The contravariant long exact Ext sequence of the short exact sequence
(`lem-weil-pbc-ext-long-exact-first-variable`, 065P) gives the exact segment
`Ext^i(M, N) → Ext^i(M', N) → Ext^(i+1)(M'', N)`, whose outer terms vanish, so
`Ext^(m+1)(M', N) = 0`. As `N` is arbitrary, 065R in its Ext-vanishing-to-resolution
direction gives a resolution of `M'` of length at most `m`. The module universe
`max u v` is the one of 065R. -/
theorem projectiveDimensionLE_of_shortExact
    {R : Type u} [CommRing R] (m : ℕ)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact)
    (h₂ : ModuleCat.HasProjectiveResolutionLE S.X₂ m)
    (h₃ : ModuleCat.HasProjectiveResolutionLE S.X₃ (m + 1)) :
    ModuleCat.HasProjectiveResolutionLE S.X₁ m := by
  sorry

end Ring
