/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerNerveTransport

/-! # Localization before the Kummer boundary pullback
Source: direct-image proof (3), localization and its actual counit mate.
(blueprint: def-sfb-kummer-local-source).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The global open direct image restricted to the entire supplied scheme.
Source: direct-image proof (3), derived sheaf rather than geometric stalks
(blueprint: def-sfb-kummer-local-source). -/
def kummerOpenImage {W Y S : Scheme.{u}} (a : W ⟶ Y) (s : S ⟶ Y)
    (L : KummerModules Λ W) : DerivedCategory (KummerModules Λ S) :=
  (upperStar Λ s).mapDerivedCategory.obj
    ((moduleObjectDerivedPushforward Λ a).obj ((DerivedCategory.singleFunctor _ 0).obj L))

/-- The localized open, formed before pulling back to the boundary stratum.
Source: direct-image proof (3), localization before boundary restriction
(blueprint: def-sfb-kummer-local-source). -/
abbrev kummerLocalOpen {W Y U : Scheme.{u}} (a : W ⟶ Y) (f : U ⟶ Y) := pullback f a

/-- The actual localization map is the base-change mate of the open direct-image
counit, followed by exact boundary pullback.
Source: direct-image proof (3), derived slice localization
(blueprint: def-sfb-kummer-local-source). -/
def kummerLocalizationMap {W Y U S : Scheme.{u}}
    (a : W ⟶ Y) (f : U ⟶ Y) (s : S ⟶ U) (L : KummerModules Λ W) :
    kummerOpenImage Λ a (s ≫ f) L ⟶
      kummerOpenImage Λ (pullback.fst f a) s
        ((upperStar Λ (pullback.snd f a)).obj L) :=
  ((kummerDerivedUpperComp Λ s f).app _).hom ≫
    (upperStar Λ s).mapDerivedCategory.map
      (kummerBaseChangeMate Λ a (pullback.snd f a) (pullback.fst f a) f
        (pullback.condition.symm)
        ((DerivedCategory.singleFunctor _ 0).obj L) ≫
      (moduleObjectDerivedPushforward Λ (pullback.fst f a)).map
        (kummerPullSingle Λ (pullback.snd f a) L).hom)

end AlgebraicGeometry.ProEtale.CondensedRing
