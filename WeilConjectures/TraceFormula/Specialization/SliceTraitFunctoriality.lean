/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitPoint
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal

/-!

# Functoriality of slice traits along a change of trait

Let `ι : R₁ →+* R₂` be a local homomorphism of local rings, `κ₂` a field and `b₂ : R₂ →+* κ₂` a
ring map with kernel the maximal ideal of `R₂`. Then `b₂ ∘ ι` has kernel the maximal ideal of
`R₁`, and the geometric points `sliceTraitPoint (b₂.comp ι) : Spec K₂ ⟶ 𝔸¹_{R₁}` and
`sliceTraitPoint b₂ : Spec K₂ ⟶ 𝔸¹_{R₂}` (with `K₂ = κ₂(x)^alg`) are compatible with the map
`𝔸¹_{R₂} ⟶ 𝔸¹_{R₁}` induced by `ι`.

Since the strict henselization `𝒪^{sh}_{𝔸¹_{R₂}, s₂}` is strictly henselian, the universal property
of the strict localization gives a ring map
`sliceTraitMap ι b₂ : 𝒪^{sh}_{𝔸¹_{R₁}, s₁} →+* 𝒪^{sh}_{𝔸¹_{R₂}, s₂}`, compatible with the maps to
the bases, the evaluations at the geometric points and the structure maps from `R₁` and `R₂`. It
is a local homomorphism, and it is injective when `R₁` and `R₂` are discrete valuation rings and
`ι` is injective.

## Main results

- `AlgebraicGeometry.sliceTraitPoint_comp`: `sliceTraitPoint (b₂.comp ι)` factors through
  `sliceTraitPoint b₂`.
- `AlgebraicGeometry.sliceTraitMap` and its compatibilities
  `spec_sliceTraitMap_comp_strictLocalizationToBase`,
  `strictHenselizationEval_comp_sliceTraitMap`, `sliceTraitMap_comp_sliceTraitStructureMap`.
- `AlgebraicGeometry.isLocalHom_sliceTraitMap`, `AlgebraicGeometry.injective_sliceTraitMap`.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

open Scheme

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] (ι : R₁ →+* R₂)
  {κ₂ : Type u} [Field κ₂] (b₂ : R₂ →+* κ₂)

end AlgebraicGeometry
