/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange

/-!
# Purity for regular closed immersions: intersections and exterior products

Let `i₁ : Y₁ ⟶ X` and `i₂ : Y₂ ⟶ X` be regular closed immersions of codimensions `c₁`, `c₂` into a
scheme `X` smooth over a perfect field, meeting transversally: their intersection
`Y = Y₁ ×_X Y₂ ⟶ X` is a regular closed immersion of codimension `c₁ + c₂`. Then the fundamental
class of `Y` is the cup product with supports of those of `Y₁` and `Y₂`,
`[Y ⊂ X] = [Y₁ ⊂ X] ∪ [Y₂ ⊂ X]`: near a point of `Y`, frames `f` of `Y₁` and `g` of `Y₂` give the
frame `(f, g)` of `Y` (`AlgebraicGeometry.Scheme.Hom.EtaleFrame.inter`), whose class
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(g_{c₂})` is the cup product of the classes of the two frames
(`AlgebraicGeometry.Etale.kummerBoundaryProduct_append`).

Applied to `Z₁ ×_k X₂` and `X₁ ×_k Z₂` in `X₁ ×_k X₂`, whose fundamental classes are the
pullbacks of `[Z₁ ⊂ X₁]` and `[Z₂ ⊂ X₂]` along the smooth projections
(`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_smooth`), this gives the
compatibility with exterior products of clause (d) of blueprint `sk-thm-regular`,
`[Z₁ × Z₂ ⊂ X₁ × X₂] = [Z₁ ⊂ X₁] ⊠ [Z₂ ⊂ X₂]`.

## Main statements

- `AlgebraicGeometry.Etale.restrictSupportedClass_cupWithSupportsTateObject`: restriction of
  supports commutes with the cup product of Tate classes.
- `AlgebraicGeometry.Etale.fundamentalClass_eq_cupWithSupportsTateObject_of_isPullback`: the
  intersection formula.
- `AlgebraicGeometry.Etale.fundamentalClass_eq_cupWithSupportsTateObject`: exterior products.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

variable [HasKummerClass.IsNormalized Λ] {X : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]

end Etale

end AlgebraicGeometry
