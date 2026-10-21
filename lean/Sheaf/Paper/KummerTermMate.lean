/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerNormalizedComparison
public import Sheaf.Paper.ProfiniteCoefficientLinearization
public import Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # The actual counit mate in one root-nerve term
Source: direct-image proof (3), full-tower restriction of sections.
(blueprint: def-sfb-kummer-term-mate).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical derived Cartesian pullback comparison of a commuting square.
Source: direct-image proof (3), base-change mate
(blueprint: def-sfb-kummer-term-mate). -/
def kummerSquarePullback {T U B S : Scheme.{u}}
    (q : T ⟶ U) (i : B ⟶ T) (π : B ⟶ S) (s : S ⟶ U)
    (w : i ≫ q = π ≫ s) :
    (upperStar Λ s).mapDerivedCategory ⋙ (upperStar Λ π).mapDerivedCategory ≅
      (upperStar Λ q).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarComp Λ π s).symm ≪≫ upperStarCongr Λ w.symm ≪≫
        upperStarComp Λ i q) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- This is the adjunct of the actual pulled-back direct-image counit.
Source: direct-image proof (3), term normalization
(blueprint: def-sfb-kummer-term-mate). -/
def kummerBaseChangeMate {T U B S : Scheme.{u}}
    (q : T ⟶ U) (i : B ⟶ T) (π : B ⟶ S) (s : S ⟶ U)
    (w : i ≫ q = π ≫ s) (N : DerivedCategory (KummerModules Λ T)) :
    (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ q).obj N) ⟶
      (moduleObjectDerivedPushforward Λ π).obj
        ((upperStar Λ i).mapDerivedCategory.obj N) :=
  (punctureDerivedAdjunction Λ π).homEquiv _ _
    ((kummerSquarePullback Λ q i π s w).hom.app
        ((moduleObjectDerivedPushforward Λ q).obj N) ≫
      (upperStar Λ i).mapDerivedCategory.map
        ((punctureDerivedAdjunction Λ q).counit.app N))

/-- The canonical direct-image composition comparison is fixed by the adjunction mate.
Source: direct-image proof (3), composition before boundary pullback
(blueprint: def-sfb-kummer-term-mate). -/
def kummerPushComposition {V T U : Scheme.{u}} (j : V ⟶ T) (q : T ⟶ U) :
    moduleObjectDerivedPushforward Λ (j ≫ q) ≅
      moduleObjectDerivedPushforward Λ j ⋙ moduleObjectDerivedPushforward Λ q :=
  conjugateIsoEquiv (punctureDerivedAdjunction Λ (j ≫ q))
    ((punctureDerivedAdjunction Λ q).comp (punctureDerivedAdjunction Λ j))
    ((Functor.mapDerivedCategoryNatIso (upperStarComp Λ j q) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm)

/-- The full-to-punctured comparison is the actual open unit, pushed to the base.
Its inverse, when invertible, is the uniquely specified puncture-to-full term map.
Source: direct-image proof (3), inverse-unit normalization
(blueprint: def-sfb-kummer-term-mate). -/
def kummerPunctureMap {V T U S : Scheme.{u}}
    (j : V ⟶ T) (q : T ⟶ U) (s : S ⟶ U)
    (N : DerivedCategory (KummerModules Λ T)) :
    (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ q).obj N) ⟶
      (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ (j ≫ q)).obj
          ((upperStar Λ j).mapDerivedCategory.obj N)) :=
  (upperStar Λ s).mapDerivedCategory.map
    ((moduleObjectDerivedPushforward Λ q).map
        ((punctureDerivedAdjunction Λ j).unit.app N) ≫
      (kummerPushComposition Λ j q).inv.app
        ((upperStar Λ j).mapDerivedCategory.obj N))

/-- A normalized geometric term is obtained by inverting this very open unit and
then taking the actual base-change counit mate. All parameter families are retained.
Source: direct-image proof (3), term normalization
(blueprint: def-sfb-kummer-term-mate). -/
def IsKummerTermComparison {V T U B S : Scheme.{u}}
    (j : V ⟶ T) (q : T ⟶ U) (i : B ⟶ T) (π : B ⟶ S) (s : S ⟶ U)
    (w : i ≫ q = π ≫ s) (N : DerivedCategory (KummerModules Λ T))
    (e : (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ (j ≫ q)).obj
          ((upperStar Λ j).mapDerivedCategory.obj N)) ≅
      (moduleObjectDerivedPushforward Λ π).obj
        ((upperStar Λ i).mapDerivedCategory.obj N)) : Prop :=
  kummerPunctureMap Λ j q s N ≫ e.hom = kummerBaseChangeMate Λ q i π s w N

end AlgebraicGeometry.ProEtale.CondensedRing
