/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerNerveTransport
public import Sheaf.Paper.ProfiniteConstantDerivedFunctions

/-! # Normalized parameterized full-root terms
Source: direct-image proof (3), evaluation and the root-tower counit mate.
(blueprint: def-sfb-kummer-parameterized-term).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
variable (A : Ring.{u})

/-- The full parameterized root map, before puncturing.
Source: direct-image proof (3), full root terms
(blueprint: def-sfb-kummer-parameterized-term). -/
abbrev kummerFullParameterMap {T U : Scheme.{u}} (q : T ⟶ U) (P : Profinite.{u}) :=
  coefficientParameterProjection T P ≫ q

/-- The boundary map and the projection commute on the full profinite parameter object.
Source: direct-image proof (3), full-root parameter square
(blueprint: def-sfb-kummer-parameterized-term).
Proof: naturality of the parameter projection gives the square over T. Compose
with q, and use the supplied equality i q = s; associativity gives the result. -/
theorem kummerParameterSquare {T U S : Scheme.{u}}
    (q : T ⟶ U) (i : S ⟶ T) (s : S ⟶ U) (h : i ≫ q = s) (P : Profinite.{u}) :
    coefficientParameterMap i P ≫ kummerFullParameterMap q P =
      coefficientParameterProjection S P ≫ s := by
  sorry

/-- A normalized geometric term is compared with the actual universal-evaluation
map for derived internal Hom. This retains the actual full-to-punctured unit and
base-change counit on every profinite parameter, including the one-point object.
Source: direct-image proof (3), parameterized term identification
(blueprint: def-sfb-kummer-parameterized-term). -/
structure KummerParameterizedTerm {V T U S : Scheme.{u}}
    (j : V ⟶ T) (q : T ⟶ U) (i : S ⟶ T) (s : S ⟶ U)
    (h : i ≫ q = s) (P : Profinite.{u}) (M : Modules A)
    (_J : InjectiveResolution M) where
  geometric : KummerGeometricTerm A.X
    (coefficientParameterMap j P) (kummerFullParameterMap q P)
    (coefficientParameterMap i P) (coefficientParameterProjection S P) s
    (kummerParameterSquare q i s h P)
    ((derivedFromCondensed A.X (coefficientParameter T P)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M))
  parameter_iso : IsIso (ProfiniteFunctions.comparisonApp A.toMon S P
    ((DerivedCategory.singleFunctor _ 0).obj M))

/-- The actual geometric term map, with its boundary point-pullback identification.
Source: direct-image proof (3), restriction of sections on the full root tower
(blueprint: def-sfb-kummer-parameterized-term). -/
def KummerParameterizedTerm.geometricMap {V T U S : Scheme.{u}}
    (j : V ⟶ T) (q : T ⟶ U) (i : S ⟶ T) (s : S ⟶ U)
    (h : i ≫ q = s) (P : Profinite.{u}) (M : Modules A)
    (J : InjectiveResolution M) (d : KummerParameterizedTerm A j q i s h P M J) :
    (upperStar A.X s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward A.X
          (coefficientParameterMap j P ≫ kummerFullParameterMap q P)).obj
          ((upperStar A.X (coefficientParameterMap j P)).mapDerivedCategory.obj
            ((derivedFromCondensed A.X (coefficientParameter T P)).obj
              ((DerivedCategory.singleFunctor _ 0).obj M)))) ⟶
      (moduleObjectDerivedPushforward A.X (coefficientParameterProjection S P)).obj
        ((derivedFromCondensed A.X (coefficientParameter S P)).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) :=
  d.geometric.comparison.hom ≫
    (moduleObjectDerivedPushforward A.X (coefficientParameterProjection S P)).map
      ((derivedFromCondensedPullbackIso A.X
        (coefficientParameterMap i P)).hom.app ((DerivedCategory.singleFunctor _ 0).obj M))

end AlgebraicGeometry.ProEtale.CondensedRing
