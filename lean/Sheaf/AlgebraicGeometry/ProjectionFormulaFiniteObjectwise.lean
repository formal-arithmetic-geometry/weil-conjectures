/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! An objectwise split of the finite proper projection formula.

Source: Stacks Project, Tag 0F0G, Lemma 59.96.6.
(blueprint: lem-etale-proper-projection-formula-finite-objectwise)

The unbounded proper projection formula is checked on arbitrary objects of the two derived
categories. The geometric-stalk proof of Tag 0F0G applies to the finite coefficient ring and
identifies the canonical map with the corresponding fibre projection map; finite cohomological
dimension of proper geometric fibres makes that fibre map invertible. This objectwise result is
the component needed to assemble the natural isomorphism in the parent module.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The objectwise finite proper projection formula used to assemble the bifunctorial result.
(blueprint: lem-etale-proper-projection-formula-finite-objectwise) -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_of_finite [Finite Λ]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsProper g] [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app M).app L) := by
  sorry

private lemma isIso_of_isIso_app_app {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B ⥤ B} (α : F ⟶ G)
    (h : ∀ X Y, IsIso ((α.app X).app Y)) : IsIso α := by
  let (X : A) : IsIso (α.app X) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro Y
    exact h X Y
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro X
  exact inferInstance

/-- Assemble the objectwise finite projection isomorphisms into the bifunctorial one. -/
theorem finite_projection_iso [Finite Λ] {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsProper g] :
    IsIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g) := by
  exact isIso_of_isIso_app_app (rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} Λ) g)
    (fun M L => isIso_rightDerivedLowerStarProjectionMap_app_app_of_finite Λ g M L)

end AlgebraicGeometry.Etale

