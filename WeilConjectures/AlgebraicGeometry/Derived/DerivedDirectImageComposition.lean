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

Source: Stacks Project, `sites-cohomology.tex`, Lemma 0D6E and its proof;
`categories.tex`, Lemma 0DV0.

The comparisons are conjugates of the derived inverse-image comparisons, using the
composite and identity adjunctions.

## Implementation details

`derivedDirectImageComposition` is the conjugate of `cᴰ : v⁻¹u⁻¹ ≅ (u ∘ v)⁻¹`, the inverse of
`upperStarCompDerivedPlus`, with respect to the derived adjunction for the composite morphism
and the composite of the two derived adjunctions; `conjugateIsoEquiv` supplies the inverse.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The composition isomorphism `R(u ∘ v)_* ≅ Ru_* ∘ Rv_*` on bounded below derived
categories of abelian etale sheaves. Source: Stacks Project, Lemma 0D6E and its proof,
with the composite adjunction of Lemma 0DV0. -/
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
