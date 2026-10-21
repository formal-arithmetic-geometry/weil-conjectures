/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AllContinuousScalarMate
public import Sheaf.Paper.KummerTermMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Canonical coefficient maps for tame Kummer descent
Source: direct-image proof (3), scalar unit and restriction square.
(blueprint: def-sfb-kummer-scalar-restriction).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Exact restriction of coefficients on the whole derived module category.
Source: direct-image proof (3), Res
(blueprint: def-sfb-kummer-scalar-restriction). -/
abbrev kummerDerivedRestriction (X : Scheme.{u}) :
    DerivedCategory (KummerModules (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X) ⥤
      DerivedCategory (KummerModules (Profinite.continuousMapRingObj E.1) X) :=
  (Mod.comap (coefficientMap (tameBoundaryScalarMap ℓ E) X)).mapDerivedCategory

/-- The right-adjoint mate of the normalized scalar/pullback comparison.
It uses no flatness assumption on the coefficient inclusion.
Source: direct-image proof (3), scalar restriction of direct images
(blueprint: def-sfb-kummer-scalar-restriction). -/
def kummerRestrictionPushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleObjectDerivedPushforward (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f ⋙
        kummerDerivedRestriction ℓ E Y ≅
      kummerDerivedRestriction ℓ E X ⋙
        moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) f :=
  conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (tameBoundaryScalarMap ℓ E) Y)).comp
      (punctureDerivedAdjunction (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f))
    ((punctureDerivedAdjunction (Profinite.continuousMapRingObj E.1) f).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (tameBoundaryScalarMap ℓ E) X)))
    (tameBoundaryScalarPullIso ℓ E f).symm

/-- Ordinary tensor extension of L; the coefficient map is the continuous inclusion.
Source: direct-image proof (3), L_Omega
(blueprint: def-sfb-kummer-scalar-restriction). -/
def kummerOmegaModule (W : Scheme.{u})
    (L : KummerModules (Profinite.continuousMapRingObj E.1) W) :
    KummerModules (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) W :=
  (Mod.extendScalars (coefficientMap (tameBoundaryScalarMap ℓ E) W)).obj L

/-- The degree-zero scalar unit is precisely x mapped to 1 tensor x.
Source: direct-image proof (3), prescribed coefficient map
(blueprint: def-sfb-kummer-scalar-restriction). -/
def kummerScalarUnit (W : Scheme.{u})
    (L : KummerModules (Profinite.continuousMapRingObj E.1) W) :
    L ⟶ (Mod.comap (coefficientMap (tameBoundaryScalarMap ℓ E) W)).obj
      (kummerOmegaModule ℓ E W L) :=
  (Mod.extendRestrictAdjunction (coefficientMap (tameBoundaryScalarMap ℓ E) W)).unit.app L

/-- The actual coefficient arrow on the restricted open direct image, after scalar
restriction. It is induced by the ordinary tensor unit and the normalized adjunction
mate; no arbitrary arrow between the two derived objects is supplied.
Source: direct-image proof (3), left side of the scalar square
(blueprint: def-sfb-kummer-scalar-restriction). -/
def kummerSourceScalarMap {W Y S : Scheme.{u}} (a : W ⟶ Y) (s : S ⟶ Y)
    (L : KummerModules (Profinite.continuousMapRingObj E.1) W) :
    (upperStar (Profinite.continuousMapRingObj E.1) s).mapDerivedCategory.obj
      ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) a).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) ⟶
    (kummerDerivedRestriction ℓ E S).obj
      ((upperStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) a).obj
          ((DerivedCategory.singleFunctor _ 0).obj (kummerOmegaModule ℓ E W L)))) :=
  (upperStar (Profinite.continuousMapRingObj E.1) s).mapDerivedCategory.map
    ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) a).map
      ((DerivedCategory.singleFunctor _ 0).map (kummerScalarUnit ℓ E W L) ≫
        ((Mod.comap (coefficientMap (tameBoundaryScalarMap ℓ E) W)).mapDerivedCategorySingleFunctor
          0).inv.app (kummerOmegaModule ℓ E W L)) ≫
      (kummerRestrictionPushIso ℓ E a).inv.app
        ((DerivedCategory.singleFunctor _ 0).obj (kummerOmegaModule ℓ E W L))) ≫
    (derivedComapUpperStarIso (tameBoundaryScalarMap ℓ E) s).inv.app _

end AlgebraicGeometry.ProEtale.CondensedRing
