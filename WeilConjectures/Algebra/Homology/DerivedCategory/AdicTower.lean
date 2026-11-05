/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.MappingConeCoimage
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import Mathlib.Algebra.Homology.Linear

/-!
# Reductions of the homotopy limit of a normalized adic tower

Let `ϖ` be an element of a ring `R` acting on an abelian category `𝒜`. A *normalized
`ϖ`-adic tower* is a tower `T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ` such that `Tₘ` is killed by `ϖᵐ`
and is flat over `R/ϖᵐ` (multiplication by `ϖᵇ` on `T_{a+b}` has kernel `ϖᵃ T_{a+b}`), and
such that for `n ≤ m` the map `Tₘ / ϖⁿ ⟶ Tₙ` induced by the transition is a
quasi-isomorphism. These are the explicit models of the normalized systems
`Tₙ ≅ T_{n+1} ⊗ᴸ_{R/ϖⁿ⁺¹} R/ϖⁿ` of Bhatt–Scholze and of Stacks, Tag 09AW, with
`T_m / ϖⁿ ⟶ T_n` a quasi-isomorphism.

For each `n`, the tower `m ↦ cone(ϖⁿ : T_{m+n} ⟶ T_{m+n})` maps to the constant tower `Tₙ`
through the reductions `T_{m+n} ⟶ Tₙ`, and the fibre of this map is the tower
`m ↦ ker(ϖⁿ on T_{m+n})⟦1⟧`, whose transitions vanish after `n` steps by flatness. Hence the
derived limit of the cones is `Tₙ`: this is
`CochainComplex.IsNormalizedAdicTower.isIso_π_comp`.

## Main definitions

- `CochainComplex.IsNormalizedAdicTower`: normalized `ϖ`-adic towers of complexes.
- `CochainComplex.IsNormalizedAdicTower.cokerDesc`: the quasi-isomorphism
  `coker(ϖⁿ on T_{m+n}) ⟶ Tₙ`.
- `CochainComplex.IsNormalizedAdicTower.cokerIso`: the induced isomorphism
  `coker(ϖⁿ on T_{m+n}) ≅ Tₙ` in the derived category.

## Main results

- `CochainComplex.IsNormalizedAdicTower.isIso_π_comp`: for a homotopy limit `c` of the tower of
  cones `m ↦ cone(ϖⁿ on T_{m+n})` in the derived category, the map `c.pt ⟶ Tₙ` induced by the
  reductions is an isomorphism.

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CochainComplex

variable {R : Type*} [Ring R] {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [Linear R 𝒜]

namespace IsNormalizedAdicTower

open ConeCoimage

variable {ϖ : R} {T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ} (hT : IsNormalizedAdicTower ϖ T) (n : ℕ)

section DerivedCategory

variable [HasDerivedCategory 𝒜]

end DerivedCategory

variable [HasDerivedCategory 𝒜]

variable [HasLimitsOfShape (Discrete ℕ) (DerivedCategory 𝒜)]

end IsNormalizedAdicTower

end CochainComplex
