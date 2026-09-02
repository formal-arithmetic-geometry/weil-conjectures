/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!

# Sheaves on an essentially small site with values in a Grothendieck abelian category

Mathlib's `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall` shows that the
category of `A`-valued sheaves on an essentially `w`-small site is Grothendieck abelian when
`A` is, but it asks for sheafification on the small model of the site and for the limits
indexed by the comma categories of the small model. Both follow from sheafification on the
site itself and Grothendieck abelianness of `A`: `HasSheafify` transports along the
equivalence with the small model (`CategoryTheory.Equivalence.hasSheafify`), and the comma
categories are essentially `w`-small. This file packages that reduction.

## Main results

- `CategoryTheory.hasSheafify_inducedTopology_equivSmallModel`: sheafification on a site
  transports to the induced topology on its small model.
- `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify`: the
  category of `A`-valued sheaves on an essentially small site is Grothendieck abelian, for
  `A` Grothendieck abelian with sheafification on the site.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₂} [Category.{v₂} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C)
  (A : Type u₁) [Category.{v₁} A]

/-- Sheafification on a site transports to the induced topology on its small model. -/
lemma hasSheafify_inducedTopology_equivSmallModel [HasSheafify J A] :
    HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J) A :=
  have : (equivSmallModel.{w} C).symm.inverse.IsDenseSubsite J
      ((equivSmallModel.{w} C).inverse.inducedTopology J) :=
    inferInstanceAs ((equivSmallModel.{w} C).functor.IsDenseSubsite _ _)
  (equivSmallModel.{w} C).symm.hasSheafify _ J A

/-- The category of `A`-valued sheaves on an essentially `w`-small site is Grothendieck
abelian, for a Grothendieck abelian category `A` (of size `w`) with sheafification on the
site: the sheafification transports to the small model and the comma categories of the
small model are essentially `w`-small, so Mathlib's
`Sheaf.isGrothendieckAbelian_of_essentiallySmall` applies. -/
lemma Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasSheafify J A] :
    IsGrothendieckAbelian.{w} (Sheaf J A) :=
  have := hasSheafify_inducedTopology_equivSmallModel.{w} J A
  have : ∀ X : Cᵒᵖ, HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op) A :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  Sheaf.isGrothendieckAbelian_of_essentiallySmall J A

end CategoryTheory
