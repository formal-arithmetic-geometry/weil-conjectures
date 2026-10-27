module

public import Sheaf.AlgebraicGeometry.GroupScheme.AffineReflectionDominantDescent

/-! # Affine-weight orders and shifted character actions

Source: Andersen, The strong linkage principle (1980), Definition 1, p.54;
Milne, Algebraic Groups (2017), Sections 21.1--21.2.
(blueprint: def-sfb-affine-weight-order-action)

The eight definitions of this node are the published declarations of
`Sheaf.AlgebraicGeometry.GroupScheme.AffineReflectionDominantDescent`, reexported here
unchanged: `AffineWeight.LE` (the difference is a nonnegative integral sum of simple roots),
`AffineWeight.LT` (dominance with unequal weights), `AffineWeight.Dominant` (the closed
rho-shifted chamber), `AffineWeight.reflectionDot` (`s_α · x = s_α(x+ρ) - ρ`),
`AffineWeight.Edge` (an affine lowering edge `y = s_β · x + npβ`, `β > 0`, `n ≥ 0`,
`y ≤ x`), `AffineWeight.Linked` (its reflexive transitive closure), `AffineWeight.dot`
(the rho-shifted action of a given action) and `AffineWeight.characterAction`
(`w χ = χ ∘ a(w)⁻¹` on the characters of the torus).
They are not redeclared, so that one definition per notion is kept.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

namespace AffineWeight

/-- The action of the actual normalizer quotient on characters under its descriptive name:
the transparent name of the published `AffineWeight.characterAction`, pulling a character
back along the inverse torus automorphism, `(w χ)(t) = χ(a(w)⁻¹ t)`.
Source: Andersen (1980), p.54; Milne, 21.1--21.2
(blueprint: def-sfb-affine-weight-order-action). -/
abbrev normalizerCharacterAction {F : Type u} [Field F]
    {T S : Grp (Over (Spec (.of F)))} (iT : T ⟶ S)
    (a : RankOneRoots.Weyl iT →* Aut T) (g : RankOneRoots.Weyl iT)
    (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) :
    Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :=
  characterAction iT a g χ

end AffineWeight

end AlgebraicGeometry
