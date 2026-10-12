/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Augmentation square for degree zero resolution maps

Source: Stacks Project, Tags 01F8, 01F9 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-zero-augmentation).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-zero resolution formula commutes with the canonical augmentations.
Source: Stacks Project, Cohomology of Sheaves, Remark 01FB, equation-choice;
Mathlib CategoryTheory.Abelian.RightDerived, toRightDerivedZero_eq
(blueprint: lem-weil-pbc-module-cohomology-fmap-zero-augmentation).

Proof: express each toRightDerivedZero using its resolution by
InjectiveResolution.toRightDerivedZero_eq. Before the inverse vertical map is
applied, both routes send a section s of G to the zero-cycle represented by
β⁰(s_J(s)): D.compatible identifies this with lambda⁰(h_*s_I(φ(s))).
The comparison D.a.inv is the canonical restriction along h⁻¹(Y) = X by
D.sections, so it identifies the latter section with s_I(φ_Y(s)) on X.
Naturality of cyclesMap and homologyπ transfers the augmentation equation to
H⁰. The vertical homology map is invertible by D.invertible; compose with its
inverse and cancel. Finally cancel the two resolution comparison isomorphisms.
The result is the stated augmentation square; left exactness is only needed
later to invert its two augmentation maps. -/
theorem ModuleCohomologyFMapData.map_zero_augmentation {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) :
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).toRightDerivedZero.app G) ≫
      D.map 0 =
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫
      (forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F) :=
  by sorry

end AlgebraicGeometry.Scheme.Modules
