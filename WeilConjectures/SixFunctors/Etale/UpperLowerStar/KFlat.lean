/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!

# The pullback `g^*` preserves K-flat complexes

The derived pullback `Lg^*` on étale sheaves is oplax monoidal for the derived tensor
product, `Lg^*(K ⊗ᴸ L) ⟶ Lg^*K ⊗ᴸ Lg^*L`, and this comparison map is the input for the
projection formula. It is computed on K-flat resolutions, so its construction needs the
pullback `g^*` to send K-flat complexes of étale sheaves to K-flat complexes. We record this
as the hypothesis class `AlgebraicGeometry.Etale.UpperStarPreservesKFlat A` on the
coefficient category `A`, quantified over all morphisms of schemes.

For `A = ModuleCat.{u + 1} Λ` the hypothesis holds: K-flatness of a complex of étale sheaves
can be checked on geometric stalks, and `g^*` preserves stalks. For a general coefficient
category no proof is known, so the class is a hypothesis, not an axiom: nothing in this
file provides an instance of it.

## Main definitions

- `AlgebraicGeometry.Etale.UpperStarPreservesKFlat`: for every morphism of schemes `g`,
  the pullback `g^*` on `A`-valued étale sheaves preserves K-flat complexes.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- The coefficient category `A` has the property that for every morphism of schemes
`g : X ⟶ Y`, the pullback `g^*` on `A`-valued étale sheaves sends K-flat complexes to
K-flat complexes, for the monoidal structure
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall` on étale
sheaves.

This is what makes the derived pullback `Lg^*` oplax monoidal for the derived tensor
product, which is needed to construct the projection formula map. It holds for
`A = ModuleCat.{u + 1} Λ`, where K-flatness is checked on geometric stalks and `g^*`
preserves stalks. It is a hypothesis on `A`, not an axiom: no instance is provided for a
general `A`. Like `CategoryTheory.HasSmallSiteSheafify`, it is used through an instance
keyed on the functor, `AlgebraicGeometry.Etale.preservesKFlat_upperStar`. -/
class Etale.UpperStarPreservesKFlat : Prop where
  preservesKFlat {X Y : Scheme.{u}} (g : X ⟶ Y) : ((g)^*[A]).PreservesKFlat

/-- Under `Etale.UpperStarPreservesKFlat A`, the pullback `g^*` on étale sheaves preserves
K-flat complexes. -/
instance Etale.preservesKFlat_upperStar [Etale.UpperStarPreservesKFlat A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) : ((g)^*[A]).PreservesKFlat :=
  Etale.UpperStarPreservesKFlat.preservesKFlat g

end AlgebraicGeometry
