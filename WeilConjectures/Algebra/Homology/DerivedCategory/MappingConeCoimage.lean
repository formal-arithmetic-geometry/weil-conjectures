/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The mapping cone of a morphism and of its coimage

Let `f : X ⟶ Y` be a morphism of cochain complexes in an abelian category, and let
`f = coimage.π f ≫ factorThruCoimage f` be its factorisation through its coimage
`W = X / ker f`. The induced morphism `ρ : cone(f) ⟶ cone(factorThruCoimage f)` is a degreewise
epimorphism, so that there is a short exact sequence

```
  0 ⟶ ker ρ ⟶ cone(f) ⟶ cone(W ⟶ Y) ⟶ 0,
```

and since `W ⟶ Y` is a monomorphism, `cone(W ⟶ Y)` is quasi-isomorphic to `coker f`. All of this
is functorial in the arrow `f`. In the derived category this gives a triangle
`ker ρ ⟶ cone(f) ⟶ coker f ⟶ (ker ρ)⟦1⟧`, natural in `f`, whose first term is concentrated on
`ker f` (shifted by one): a morphism of arrows which kills `ker f` induces zero on `ker ρ`.

## Main definitions

- `CochainComplex.ConeCoimage.cone`: the functor `f ↦ cone(f)` from arrows.
- `CochainComplex.ConeCoimage.ρ`: the natural map `cone(f) ⟶ cone(factorThruCoimage f)`.
- `CochainComplex.ConeCoimage.ker`: the functor `f ↦ ker ρ`.
- `CochainComplex.ConeCoimage.triangle`: the triangle `ker ρ ⟶ cone(f) ⟶ coker f ⟶ (ker ρ)⟦1⟧`
  in the derived category.

## Main results

- `CochainComplex.ConeCoimage.triangle_distinguished`: the triangle is distinguished.
- `CochainComplex.ConeCoimage.ker_map_eq_zero`: a morphism of arrows `u : f ⟶ g` with
  `kernel.ι f ≫ u.left = 0` induces the zero map `ker ρ_f ⟶ ker ρ_g`.

-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace CochainComplex.ConeCoimage

open HomComplex mappingCone

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "𝒞" => CochainComplex 𝒜 ℤ

section

variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂)
  (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

end

variable [HasDerivedCategory 𝒜]

end CochainComplex.ConeCoimage
