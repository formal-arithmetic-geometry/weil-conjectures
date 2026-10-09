/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
public import WeilConjectures.WeilSheaf.Triangle

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

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.shortExact_boundaryShortComplex` and
  `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.boundaryTriangle_distinguished`: the sequence
  `0 → j_!M → j_*M → B → 0` is short exact, and its rotated triangle
  `B → j_!M[1] → j_*M[1] → B[1]` is distinguished, as is its Fourier transform
  (`…LisseOnDenseOpen.fourierTransform_mapTriangle_boundaryTriangle_distinguished`).
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection`: the exact sequence, the
  comparison isomorphisms with the transforms, and the square identifying its epimorphism with
  the transform of `j_!M[1] → j_*M[1]`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_fourierCorrection`: it exists.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection.isLisse` and
  `…FourierCorrection.hasWeightsAtMost`: the correction sheaf is lisse of weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

namespace WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (ψ : AddChar k₀ (PadicAlgCl l))

section Boundary

variable (D : LisseOnDenseOpen k₀ l)

/-- The sequence `0 → j_!M → j_*M → B → 0` of Weil sheaves on the affine line, `B` being the
boundary sheaf. -/
noncomputable def boundaryShortComplex : ShortComplex (WeilSheaf k₀ l (affineLine k₀)) :=
  ShortComplex.mk ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf) (cokernel.π _)
    (cokernel.condition _)

/-- The sequence `0 → j_!M → j_*M → B → 0` is short exact: `j_!M → j_*M` is a monomorphism
(`AlgebraicGeometry.WeilSheaf.mono_extensionByZeroToDirectImage_app`) and `B` is its cokernel.
(blueprint: `sk-p-dl-a1-correction`) -/
lemma shortExact_boundaryShortComplex : D.boundaryShortComplex.ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (WeilSheaf.mono_extensionByZeroToDirectImage_app D.j D.sheaf)
    (inferInstanceAs (Epi (cokernel.π _)))

/-- The rotated triangle `B → j_!M[1] → j_*M[1] → B[1]` of the sequence
`0 → j_!M → j_*M → B → 0`, whose middle arrow is `-(j_!M[1] → j_*M[1])`. -/
noncomputable def boundaryTriangle : Triangle (WeilComplex k₀ l (affineLine k₀)) :=
  (WeilSheaf.singleTriangle D.shortExact_boundaryShortComplex).rotate.rotate

lemma boundaryTriangle_mor₂ :
    D.boundaryTriangle.mor₂ = -D.shiftedExtensionByZeroToMiddleExtension :=
  rfl

/-- The rotated triangle `B → j_!M[1] → j_*M[1] → B[1]` is distinguished.
(blueprint: `sk-p-dl-a1-correction`) -/
lemma boundaryTriangle_distinguished : D.boundaryTriangle ∈ distTriang _ :=
  rot_of_distTriang _ (rot_of_distTriang _
    (WeilSheaf.singleTriangle_distinguished D.shortExact_boundaryShortComplex))

/-- The Fourier transform of the rotated triangle `B → j_!M[1] → j_*M[1] → B[1]` is
distinguished, the transform being a triangulated functor. (blueprint: `sk-p-dl-a1-correction`) -/
lemma fourierTransform_mapTriangle_boundaryTriangle_distinguished :
    (fourierTransform ψ).mapTriangle.obj D.boundaryTriangle ∈ distTriang _ :=
  (fourierTransform ψ).map_distinguished _ D.boundaryTriangle_distinguished

end Boundary

/--
The zero-extension comparison datum for `D` and a Fourier partner `D'`: a short exact sequence
`0 → B' → G → j'_*M' → 0` of Weil sheaves on the dual line together with the isomorphisms
that identify `G[1]` with `FT_ψ(j_!M[1])`, `B'[1]` with `FT_ψ(B)` and `(j'_*M')[1]` with
`FT_ψ(j_*M[1])`, where `B = j_*M / j_!M` is the boundary sheaf of `D`, such that the epimorphism
`G → j'_*M'` is the transform of `j_!M[1] → j_*M[1]`:

```
  FT_ψ(B) ≃ B'[1]

  FT_ψ(j_!M[1]) ──FT_ψ(can[1])──▶ FT_ψ(j_*M[1])
        │ ≃                             │ ≃
        ▼                               ▼
      G[1] ────────────g[1]──────────▶ X₃[1]

  0 ──▶ B' ──▶ G ──g──▶ X₃ ≃ j'_*M' ──▶ 0
```

The square pins the sequence down: a short exact sequence is determined up to isomorphism by its
epimorphism, `B'` being its kernel, so the sequence is the one obtained from the transform of the
rotated triangle `B → j_!M[1] → j_*M[1] → B[1]` and not, say, a split one. The square is stated
for the middle arrow of the rotated triangle only: the first arrow `B → j_!M[1]` is the connecting
morphism of `0 → j_!M → j_*M → B → 0`, whose formation needs `j_!M → j_*M` to be a
monomorphism, and comparing whole triangles needs a shift-compatibility of the transform; the
square already determines the sequence. (blueprint: `sk-p-dl-a1-correction`)
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
  /-- The transform of the middle extension is the shifted third term. -/
  isoMiddleExtension : (fourierTransform ψ).obj D.middleExtension ≅
    (WeilSheaf.toComplex.obj seq.X₃)⟦(1 : ℤ)⟧
  /-- The epimorphism `G → j'_*M'` of the sequence is the transform of `j_!M[1] → j_*M[1]`. -/
  fourierTransform_map_comp_isoMiddleExtension_hom :
    (fourierTransform ψ).map D.shiftedExtensionByZeroToMiddleExtension ≫
        isoMiddleExtension.hom =
      isoExtensionByZero.hom ≫ (WeilSheaf.toComplex.map seq.g)⟦(1 : ℤ)⟧'

/-- For an irreducible nonexceptional `M` and a Fourier partner `D'` of `D`, the zero-extension
comparison datum exists. (blueprint: `sk-p-dl-a1-correction`) -/
theorem nonempty_fourierCorrection (hψ : ψ ≠ 1) (D D' : LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse)
    (hne : D.sheaf.IsNonexceptional ψ D.j) (hFT : D.IsFourierPartner ψ D') :
    Nonempty (FourierCorrection ψ D D') := by
  -- TODO: Step 5 of `sk-p-dl-a1-correction`: `G = 𝓗⁻¹ FT_ψ(j_!M[1])` and
  -- `B' = 𝓗⁻¹ FT_ψ(B)`. The maps of the sequence come from the transform of the rotated
  -- triangle `B'[1] → FT_ψ(j_!M[1]) → (j'_*M')[1] →`; it needs the transforms of the boundary
  -- skyscrapers (Step 2, `lem-fd-first-formula`), which are not available for Weil complexes.
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
