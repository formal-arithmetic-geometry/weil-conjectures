/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerConstantNerveTerm
public import Sheaf.Paper.KummerParameterizedTerm

/-! # Actual counit-normalized maps from root-nerve terms
Source: direct-image proof (3), canonical coordinate and coefficient transport.
(blueprint: def-sfb-kummer-nerve-geometric-map).
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

/-- The exact derived pullback identification on a root-coordinate term.
Source: direct-image proof (3), actual punctured representation identification
(blueprint: def-sfb-kummer-nerve-geometric-map). -/
def kummerNerveDerivedIso {V T W : Scheme.{u}} {G : Profinite.{u}} [CommGroup G]
    [IsTopologicalGroup G] (action : ProfiniteCoefficientAction V G) (v : V ⟶ W)
    (h : action.act ≫ v = coefficientParameterProjection V G ≫ v)
    (coords : KummerNerveCoordinateData action v h)
    (j : V ⟶ T) (L : KummerModules A.X W) (M : Modules A)
    (e : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M) (n : ℕ) :=
  kummerSquareDerivedModuleIso A (coords.map n) ((cechOver v).obj (op (.mk n))).hom
    (coefficientParameterProjection V (power G n)) v (coords.over n) L M e
    (coefficientParameterMap j (power G n))

/-- Equality of the actual structural maps in a parameterized nerve coordinate.
Source: direct-image proof (3), actual augmented root nerve
(blueprint: def-sfb-kummer-nerve-geometric-map).
Proof: apply the over-base equation of the canonical nerve coordinate map and
compose with a. Parameter-projection naturality and j q = v a identify the other
side with the same composite. -/
theorem kummerNerveMap_toBase {V T W U : Scheme.{u}} {G : Profinite.{u}} [CommGroup G]
    [IsTopologicalGroup G] (action : ProfiniteCoefficientAction V G) (v : V ⟶ W)
    (h : action.act ≫ v = coefficientParameterProjection V G ≫ v)
    (coords : KummerNerveCoordinateData action v h)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (hj : j ≫ q = v ≫ a) (n : ℕ) :
    coords.map n ≫ kummerNerveToBase a v n =
      coefficientParameterMap j (power G n) ≫ kummerFullParameterMap q (power G n) := by
  sorry

/-- The map from an actual derived nerve term is restriction along the canonical
root coordinates followed by the inverse puncture unit and actual counit mate.
Source: direct-image proof (3), normalized term comparison
(blueprint: def-sfb-kummer-nerve-geometric-map). -/
def kummerNerveGeometricMap {V T W U S : Scheme.{u}} {G : Profinite.{u}} [CommGroup G]
    [IsTopologicalGroup G] (action : ProfiniteCoefficientAction V G) (v : V ⟶ W)
    (h : action.act ≫ v = coefficientParameterProjection V G ≫ v)
    (coords : KummerNerveCoordinateData action v h)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (hj : j ≫ q = v ≫ a)
    (i : S ⟶ T) (s : S ⟶ U) (hi : i ≫ q = s)
    (L : KummerModules A.X W) (M : Modules A)
    (e : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M)
    (J : InjectiveResolution M) (n : ℕ)
    (d : KummerParameterizedTerm A j q i s hi (power G n) M J) :
    (upperStar A.X s).mapDerivedCategory.obj
      ((moduleObjectDerivedPushforward A.X (kummerNerveToBase a v n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((upperStar A.X ((cechOver v).obj (op (.mk n))).hom).obj L))) ⟶
    (moduleObjectDerivedPushforward A.X (coefficientParameterProjection S (power G n))).obj
      ((derivedFromCondensed A.X (coefficientParameter S (power G n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) :=
  kummerImageTransport A.X (coords.map n)
    (kummerNerveToBase a v n)
    (coefficientParameterMap j (power G n) ≫ kummerFullParameterMap q (power G n)) s
    (kummerNerveMap_toBase action v h coords j q a hj n)
    _ _ (kummerNerveDerivedIso A action v h coords j L M e n) ≫
    d.geometricMap A j q i s hi (power G n) M J

end AlgebraicGeometry.ProEtale.CondensedRing
