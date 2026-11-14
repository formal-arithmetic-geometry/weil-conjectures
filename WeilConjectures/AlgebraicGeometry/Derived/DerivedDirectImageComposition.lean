/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-!
# Composition isomorphisms of derived direct images

The comparisons are conjugates of the derived inverse-image comparisons, using the
composite and identity adjunctions.

## References

* Stacks Project, Tags 0D6E, 0DV0
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The composition isomorphism `R(u ∘ v)_* ≅ Ru_* ∘ Rv_*` on bounded below derived
categories of abelian etale sheaves: the conjugate of `cᴰ : v⁻¹u⁻¹ ≅ (u ∘ v)⁻¹`, the inverse of
`upperStarCompDerivedPlus`, with respect to the derived adjunction for the composite morphism
and the composite of the two derived adjunctions. -/
noncomputable def derivedDirectImageComposition {X Y Z : Scheme.{u}}
    (u₀ : Y ⟶ X) (v₀ : Z ⟶ Y) :
    rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (v₀ ≫ u₀) ≅
      rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v₀ ⋙
        rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} u₀ :=
  conjugateIsoEquiv
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (v₀ ≫ u₀)).derivedPlus
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u₀).derivedPlus.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v₀).derivedPlus)
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} v₀ u₀ (v₀ ≫ u₀) rfl).symm

end AlgebraicGeometry.Etale
