/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerNormalizedChart
public import Sheaf.Paper.KummerInvariantScalarMap
public import Sheaf.Paper.KummerLocalSource

/-! # Global normalization of a stratum chart
Source: direct-image proof (3), localization before the boundary pullback.
(blueprint: def-sfb-kummer-global-chart).
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

/-- One chart comparison has the actual global open-image source. Its normalization
is localization by the canonical counit mate followed by the normalized local nerve
comparison. Source: direct-image proof (3), whole-stratum result
(blueprint: def-sfb-kummer-global-chart). -/
structure KummerGlobalChart (B : Model A G) {V T W Y U S : Scheme.{u}}
    (a : W ⟶ Y) (f : U ⟶ Y) (s : S ⟶ U)
    (action : ProfiniteCoefficientAction V G) (v : V ⟶ kummerLocalOpen a f)
    (h : action.act ≫ v = coefficientParameterProjection V G ≫ v)
    (j : V ⟶ T) (q : T ⟶ U)
    (hj : j ≫ q = v ≫ pullback.fst f a)
    (i : S ⟶ T) (hi : i ≫ q = s)
    (L : KummerModules A.X W) (M : Equivariant A G) where
  normalized : KummerNormalizedChart A G B action v h j q (pullback.fst f a) hj i s hi
    ((upperStar A.X (pullback.snd f a)).obj L) M
  localization_iso : IsIso (kummerLocalizationMap A.X a f s L)
  comparison : kummerOpenImage A.X a (s ≫ f) L ≅ kummerInvariantObject A G B S M
  normalization : comparison.hom = kummerLocalizationMap A.X a f s L ≫
    normalized.descent.comparison.hom

end AlgebraicGeometry.ProEtale.CondensedRing
