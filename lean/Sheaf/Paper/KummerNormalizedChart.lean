/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerResolvedDescent
public import Sheaf.Paper.KummerNerveGeometricMap

/-! # A whole-stratum comparison fixed by its actual term mates
Source: direct-image proof (3), whole augmented Kummer nerve and its counit.
(blueprint: def-sfb-kummer-normalized-chart).
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
variable (A : Ring.{u}) (G : Profinite.{u}) [CommGroup G] [IsTopologicalGroup G]
  [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- A normalized comparison is a coherent resolved descent whose every column is
fixed by the actual root-coordinate restriction, puncture unit, and counit mate.
The equation holds on the full parameter object G^n, and the coherent roof preserves
all faces and degeneracies. Source: direct-image proof (3)
(blueprint: def-sfb-kummer-normalized-chart). -/
structure KummerNormalizedChart (B : Model A G) {V T W U S : Scheme.{u}}
    (action : ProfiniteCoefficientAction V G) (v : V ⟶ W)
    (h : action.act ≫ v = coefficientParameterProjection V G ≫ v)
    (j : V ⟶ T) (q : T ⟶ U) (a : W ⟶ U) (hj : j ≫ q = v ≫ a)
    (i : S ⟶ T) (s : S ⟶ U) (hi : i ≫ q = s)
    (L : KummerModules A.X W) (M : Equivariant A G) where
  punctured : (upperStar A.X v).obj L ≅ ((upperStarFromPoint V).mapMod A.X).obj M.module
  coordinates : KummerNerveCoordinateData action v h
  nerve_coordinates : ∀ n : ℕ, IsIso (coordinates.map n)
  descent : KummerResolvedDescent A G B a s v L M
  terms : ∀ n : ℕ, KummerParameterizedTerm A j q i s hi (power G n) M.module
    descent.barResolution.underlying
  column_square : ∀ n : ℕ,
    DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        ((((evaluation SimplexCategory (KummerModules A.X S)).obj (.mk n)).mapHomologicalComplex
          (.up ℕ)).map descent.roof.cech) ComplexShape.embeddingUpNat) ≫
      kummerCechColumnMap A.X a s v descent.resolution n ≫
      kummerNerveGeometricMap A action v h coordinates j q a hj i s hi L M.module punctured
        descent.barResolution.underlying n (terms n) =
    DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        ((((evaluation SimplexCategory (KummerModules A.X S)).obj (.mk n)).mapHomologicalComplex
          (.up ℕ)).map descent.roof.bar) ComplexShape.embeddingUpNat) ≫
      kummerBarColumnEvaluation A G B S descent.actionResolution descent.barResolution n

end AlgebraicGeometry.ProEtale.CondensedRing
