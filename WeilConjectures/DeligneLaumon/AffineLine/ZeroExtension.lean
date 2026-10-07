/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension

/-!
# Comparing the transform of the zero extension with the transform of the middle extension

Rotating the triangle of `0 → j_!M → j_*M → B → 0`, where `B = j_*M / j_!M` is the punctual
boundary sheaf, gives a short exact sequence of curve perverse sheaves
`B → j_!M[1] → j_*M[1]`. Fourier exactness on the perverse heart turns it into a short exact
sequence of perverse sheaves on the dual line. Each punctual summand of `B` transforms into a
lisse Artin–Schreier kernel shifted by one, and the middle extension transforms into
`(j'_*M')[1]`, so the whole sequence is concentrated in one ordinary degree:

`0 → B' → G → j'_*M' → 0`, with `FT_ψ(j_!M[1]) ≃ G[1]` and `FT_ψ(B) ≃ B'[1]`.

The correction term `B'` is lisse on the entire dual line and, by semicontinuity of weights
at the boundary points together with the weight zero of the Artin–Schreier kernel, has weights
at most `w`.

The datum of that sequence together with the two comparison isomorphisms is bundled as
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection`, so that the correction sheaf
`B'` and its rank can be named in the weight estimate of
`WeilConjectures.DeligneLaumon.AffineLine.FourierWeight`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection`: the exact sequence and the
  two comparison isomorphisms.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_fourierCorrection`: it exists.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection.isLisse` and
  `…FourierCorrection.hasWeightsAtMost`: the correction sheaf is lisse of weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (ψ : AddChar k₀ (PadicAlgCl l))

/--
The zero-extension comparison datum for `D` and a Fourier partner `D'`: a short exact sequence
`0 → B' → G → j'_*M' → 0` of Weil sheaves on the dual line together with the two isomorphisms
that identify `G[1]` with `FT_ψ(j_!M[1])` and `B'[1]` with `FT_ψ(B)`, where `B = j_*M / j_!M`
is the boundary sheaf of `D`.

```
  FT_ψ(B) ≃ B'[1]        FT_ψ(j_!M[1]) ≃ G[1]

  0 ──▶ B' ──▶ G ──▶ j'_*M' ──▶ 0
```
(blueprint: `sk-p-dl-a1-correction`)
-/
structure FourierCorrection (D D' : LisseOnDenseOpen k₀ l) where
  /-- The short exact sequence `0 → B' → G → j'_*M' → 0` on the dual line. -/
  seq : ShortComplex (WeilSheaf k₀ l (affineLine k₀))
  /-- The sequence is short exact. -/
  shortExact : seq.ShortExact
  /-- Its third term is the middle extension of the Fourier partner. -/
  isoDirectImage : seq.X₃ ≅ D'.directImage
  /-- The transform of the shifted zero extension is the shifted middle term. -/
  isoExtensionByZero : (fourierTransform ψ).obj D.shiftedExtensionByZero ≅
    (WeilSheaf.toComplex.obj seq.X₂)⟦(1 : ℤ)⟧
  /-- The transform of the boundary sheaf is the shifted first term. -/
  isoBoundary : (fourierTransform ψ).obj (WeilSheaf.toComplex.obj D.boundarySheaf) ≅
    (WeilSheaf.toComplex.obj seq.X₁)⟦(1 : ℤ)⟧

/-- For an irreducible nonexceptional `M` and a Fourier partner `D'` of `D`, the zero-extension
comparison datum exists. (blueprint: `sk-p-dl-a1-correction`) -/
theorem nonempty_fourierCorrection (hψ : ψ ≠ 1) (D D' : LisseOnDenseOpen k₀ l) [Simple D.sheaf]
    (hne : D.sheaf.IsNonexceptional ψ) (hFT : D.IsFourierPartner ψ D') :
    Nonempty (FourierCorrection ψ D D') := by
  -- TODO: Step 5 of `sk-p-dl-a1-correction`: `G = 𝓗⁻¹ FT_ψ(j_!M[1])` and
  -- `B' = 𝓗⁻¹ FT_ψ(B)`. The maps of the sequence come from the rotated triangle
  -- `B'[1] → FT_ψ(j_!M[1]) → (j'_*M')[1] →`, which cannot be formed since `WeilComplex` is not
  -- triangulated.
  sorry

/-- The correction sheaf `B'` is lisse on the entire dual line: it is a sum of Artin–Schreier
kernels. (blueprint: `sk-p-dl-a1-correction`) -/
theorem FourierCorrection.isLisse {D D' : LisseOnDenseOpen k₀ l}
    (c : FourierCorrection ψ D D') : c.seq.X₁.IsLisse :=
  -- TODO: Step 3 of `sk-p-dl-a1-correction`: `B'` is a sum of finite direct images of
  -- Artin–Schreier twists along the finite étale maps `A'_s → A'`.
  sorry

/-- The correction sheaf `B'` has weights at most `w` when `M` is punctually `ι`-pure of weight
`w`: semicontinuity of weights at the boundary points, together with the weight zero of the
Artin–Schreier kernel. (blueprint: `sk-p-dl-a1-correction`) -/
theorem FourierCorrection.hasWeightsAtMost (ι : PadicAlgCl l →+* ℂ)
    {D D' : LisseOnDenseOpen k₀ l} (c : FourierCorrection ψ D D') {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) : c.seq.X₁.HasWeightsAtMost ι w := by
  -- TODO: Step 4 of `sk-p-dl-a1-correction` bounds the eigenvalues of `F_y` on `B'_ȳ` through
  -- the boundary semicontinuity and the weight zero of the Artin–Schreier sheaves.
  sorry

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
