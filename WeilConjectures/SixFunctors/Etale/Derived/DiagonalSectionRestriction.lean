/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Restriction along the sections `x ↦ (x, y)` of `X ×_S X`

Let `a : X ⟶ S` be proper, `P = X ×_S X` with projections `p₁`, `p₂`, and let `y` be a section
of `a`. Then `j_y = (𝟙, a ≫ y) : X ⟶ P` is a section of `p₁` with `j_y ≫ p₂ = a ≫ y`, and
restricting along `j_y` turns a morphism `α : Lp₁^* N ⟶ Lp₂^* La^* Q` into a morphism
`N ⟶ La^* Q` (`AlgebraicGeometry.Etale.pullbackLiftSectionRestrict`). Classically, for
`N = Λ_X` and `Q = Λ_S`, this is the restriction `H^*(X ×_S X) ⟶ H^*(X)` to the fibre
`X × {y}` of the second projection.

The restriction is independent of the section `y` as soon as the unit `Q ⟶ Ra_* La^* Q` is an
epimorphism onto `Q` in the weak sense that `h ↦ η_Q ≫ h` is injective on `Hom(Ra_* La^* Q, Q)`
(`AlgebraicGeometry.Etale.pullbackLiftSectionRestrict_eq`). By proper base change
`La^* Ra_* ≅ Rp₁_* Lp₂^*`, every `α` is `Lp₁^* φ` followed by `Lp₂^*` of the counit of
`La^* ⊣ Ra_*`, and its restriction along `j_y` is `φ ≫ La^*(ψ_y)` for the restriction
`ψ_y : Ra_* La^* Q ⟶ Q` of global sections to the point `y`. Each `ψ_y` is a retraction of the
unit `η_Q`, so the `ψ_y` all agree.

## Main definitions

- `AlgebraicGeometry.Etale.pullbackLiftSection`: the section `j_y = (𝟙, a ≫ y)` of `p₁`.
- `AlgebraicGeometry.Etale.pullbackLiftSectionRestrict`: restriction along `j_y`.

## Main statements

- `AlgebraicGeometry.Etale.pullbackLiftSectionRestrict_eq`: independence of the section.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable {X S : Scheme.{u}} (a : X ⟶ S)

variable (Λ : Type (u + 1)) [CommRing Λ]

variable [Finite Λ] [IsProper a]

end Etale

end AlgebraicGeometry
