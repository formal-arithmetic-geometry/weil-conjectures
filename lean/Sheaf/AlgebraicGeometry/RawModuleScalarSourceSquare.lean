/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

import Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition
import Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquareCore
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors

/-! # Source factors of the derived scalar pullback square

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-source-square).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace CategoryTheory.Functor

variable {E B : Type*} [Category E] [Category B] [Abelian E] [Abelian B]

omit [Abelian E] [Abelian B] in
private theorem source_attach
    (H : E ⥤ B) {A₁ A₂ A₃ A₄ : B} {B₁ B₂ B₃ : E}
    (f : A₁ ⟶ A₂) (p : A₂ ⟶ A₃) (v : A₃ ⟶ A₄)
    (kL : A₂ ⟶ H.obj B₂) (kE : A₁ ⟶ H.obj B₁)
    (g : B₁ ⟶ B₂) (q : B₂ ⟶ B₃) (r : H.obj B₃ ⟶ A₄)
    (ht : f ≫ kL = kE ≫ H.map g)
    (hc : p ≫ v = kL ≫ H.map q ≫ r) :
    (f ≫ p) ≫ v = kE ≫ H.map (g ≫ q) ≫ r := by
  rw [Category.assoc, hc, ← Category.assoc, ht]
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

namespace RawModuleScalarComparison

/-- Derive the fixed scalar inverse-image comparison, using composition comparisons.
(blueprint: lem-sbc-raw-scalar-source-square). -/
noncomputable abbrev derivedPullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  RawModuleScalarComparison.derivedPullbackIsoImpl Λ f

end RawModuleScalarComparison

set_option backward.isDefEq.respectTransparency true in
/-- The source square for scalar forgetting and composite inverse image.
Source: Stacks Project, Tags 03D7 and 03Q8, inverse-image composition, and the
source-factor calculation in lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-source-square).

Proof: The inverse of the scalar Kan-extension comparison commutes with the
Kan-extension unit, and the sheafification comparison commutes with the
sheafification unit. Hence pullbackIso is the mate of the scalar-forgetting
comparison on direct images. The composition unit equation for upperStarComp
then identifies the two ways of forgetting a composite inverse image.
Apply this equation to L; naturality of upperStarComp applied to t moves t
across the source comparison. Apply singleFunctor to the resulting sheaf
square. Naturality of mapDerivedCategoryPlusSingleFunctor and its compatibility
with the derived composition comparison identify the single factors with the
components of derivedPullbackIso. Cancel the single comparison isomorphisms.
This gives the displayed square. It holds for arbitrary E,L,t, including zero
objects and zero maps, and also for identity scheme arrows. No coefficient
sheaf, degree, cohomology class, or invertibility of t is used. -/
theorem rawModuleScalar_source_square
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : E ⟶ (RawModuleScalarComparison.forget Λ S).obj L) :
  let VA := (RawModuleScalarComparison.forget Λ Y').mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus
  let LB := (upperStar (ModuleCat.{u + 1} Λ) h).obj L
  let cA := scalarSourceFactor Λ h' L E t
  let cB := scalarSourceFactor Λ h L E t
  let mS := moduleSourceFactor Λ a h h' w L
  let aS := abelianSourceFactor a h h' w E
  cA ≫ VA.map mS = aS ≫ H.map cB ≫
    (RawModuleScalarComparison.derivedPullbackIso Λ a).inv.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj LB) := by
  let m := (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L
  let k := (upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app E
  let cA := (upperStar AddCommGrpCat.{u + 1} h').map t ≫
    RawModuleScalarComparison.pullback Λ h' L
  let cB := (upperStar AddCommGrpCat.{u + 1} h).map t ≫
    RawModuleScalarComparison.pullback Λ h L
  have hs : cA ≫ (RawModuleScalarComparison.forget Λ Y').map m =
      k ≫ (upperStar AddCommGrpCat.{u + 1} a).map cB ≫
        RawModuleScalarComparison.pullback Λ a
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L) :=
    Functor.source_attach (upperStar AddCommGrpCat.{u + 1} a)
      ((upperStar AddCommGrpCat.{u + 1} h').map t)
      (RawModuleScalarComparison.pullback Λ h' L)
      ((RawModuleScalarComparison.forget Λ Y').map m)
      ((upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
        ((RawModuleScalarComparison.forget Λ S).obj L)) k
      ((upperStar AddCommGrpCat.{u + 1} h).map t)
      (RawModuleScalarComparison.pullback Λ h L)
      (RawModuleScalarComparison.pullback Λ a
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj L))
      ((upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.naturality t)
      (rawModuleScalar_sheaf_composition Λ a h h' w L)
  exact Functor.plus_single_source_square_core
    (upperStar (ModuleCat.{u + 1} Λ) a) (RawModuleScalarComparison.forget Λ Y')
    (RawModuleScalarComparison.forget Λ Y) (upperStar AddCommGrpCat.{u + 1} a)
    (RawModuleScalarComparison.pullbackIso Λ a) 0 m k cA cB hs

end AlgebraicGeometry.Etale
