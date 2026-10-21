/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerGeometricColumns

/-! # Canonical transport between actual root-nerve terms
Source: direct-image proof (3), parameterized root coordinates.
(blueprint: def-sfb-kummer-nerve-transport).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Transport direct images along equality of the actual structural maps.
Source: direct-image proof (3), canonical coefficient identifications
(blueprint: def-sfb-kummer-nerve-transport). -/
def kummerPushCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    moduleObjectDerivedPushforward Λ f ≅ moduleObjectDerivedPushforward Λ g :=
  Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ h)

/-- Restriction along an actual nerve coordinate map, retaining its adjunction unit.
Source: direct-image proof (3), actual augmented Kummer nerve
(blueprint: def-sfb-kummer-nerve-transport). -/
def kummerImageTransport {V Z U S : Scheme.{u}}
    (θ : Z ⟶ V) (q : V ⟶ U) (q' : Z ⟶ U) (s : S ⟶ U) (h : θ ≫ q = q')
    (N : DerivedCategory (KummerModules Λ V))
    (N' : DerivedCategory (KummerModules Λ Z))
    (e : (upperStar Λ θ).mapDerivedCategory.obj N ≅ N') :
    (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ q).obj N) ⟶
      (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ q').obj N') :=
  kummerPunctureMap Λ θ q s N ≫
    (upperStar Λ s).mapDerivedCategory.map
      ((kummerPushCongr Λ h).hom.app _ ≫
        (moduleObjectDerivedPushforward Λ q').map e.hom)

/-- Pullback of a module in degree zero with the canonical exact-functor comparison.
Source: direct-image proof (3), degree-zero nerve terms
(blueprint: def-sfb-kummer-nerve-transport). -/
def kummerPullSingle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : KummerModules Λ Y) :
    (upperStar Λ f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ f).obj N) :=
  ((upperStar Λ f).mapDerivedCategorySingleFunctor 0).app N

/-- The canonical coefficient pullback composition comparison on derived categories.
Source: direct-image proof (3), exact Cartesian coefficient pullback
(blueprint: def-sfb-kummer-nerve-transport). -/
def kummerDerivedUpperComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar Λ (f ≫ g)).mapDerivedCategory ≅
      (upperStar Λ g).mapDerivedCategory ⋙ (upperStar Λ f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Equality of structural maps gives the canonical derived pullback identification.
Source: direct-image proof (3), actual nerve coordinates
(blueprint: def-sfb-kummer-nerve-transport). -/
def kummerDerivedUpperCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (upperStar Λ f).mapDerivedCategory ≅ (upperStar Λ g).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarCongr Λ h)

end AlgebraicGeometry.ProEtale.CondensedRing
