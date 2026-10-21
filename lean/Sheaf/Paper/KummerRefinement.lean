/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerInvariantScalarMap
public import Sheaf.Paper.KummerLocalSource
public import Sheaf.Paper.KummerGlobalChart

/-! # Canonical restriction of whole-stratum Kummer comparisons
Source: direct-image proof (3), naturality for restrictions of the covering family.
(blueprint: def-sfb-kummer-refinement).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
variable (A : Ring.{u}) (G : Profinite.{u}) [CommGroup G] [IsTopologicalGroup G]
  [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- The exact restriction comparison on ordinary derived invariants is the point
pullback comparison after the canonical localization transport.
Source: direct-image proof (3), refinement naturality
(blueprint: def-sfb-kummer-refinement). -/
def kummerInvariantPullbackIso (B : Model A G) {S S' : Scheme.{u}} (f : S' ⟶ S)
    (N : Equivariant A G) :
    (upperStar A.X f).mapDerivedCategory.obj (kummerInvariantObject A G B S N) ≅
      kummerInvariantObject A G B S' N :=
  (kummerPointPullBigPullbackIso A f).app _

/-- Each restriction carries an actual normalized global Kummer chart, and its
comparison is the exact pullback of the original chart comparison. In particular,
the restriction must still arise from the augmented root nerve and counit, rather
than merely being a morphism defined by the pullback formula.
Source: direct-image proof (3), restrictions of the covering family
(blueprint: def-sfb-kummer-refinement). -/
structure KummerRefinementNatural (B : Model A G) {V T W Y U S : Scheme.{u}}
    (a : W ⟶ Y) (f : U ⟶ Y) (s : S ⟶ U)
    (action : ProfiniteCoefficientAction V G) (v : V ⟶ kummerLocalOpen a f)
    (h : action.act ≫ v = coefficientParameterProjection V G ≫ v)
    (j : V ⟶ T) (q : T ⟶ U)
    (hj : j ≫ q = v ≫ pullback.fst f a)
    (i : S ⟶ T) (hi : i ≫ q = s)
    (L : KummerModules A.X W) (N : Equivariant A G)
    (chart : KummerGlobalChart A G B a f s action v h j q hj i hi L N) where
  restriction : ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
    KummerGlobalChart A G B a f (g ≫ s) action v h j q hj (g ≫ i)
      ((Category.assoc g i q).trans (congrArg (fun t ↦ g ≫ t) hi)) L N
  normalization : ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
    (restriction S' g).comparison.hom =
      eqToHom (congrArg (fun t ↦ kummerOpenImage A.X a t L) (Category.assoc g s f)) ≫
        ((kummerDerivedUpperComp A.X g (s ≫ f)).app _).hom ≫
          (upperStar A.X g).mapDerivedCategory.map chart.comparison.hom ≫
            (kummerInvariantPullbackIso A G B g N).hom

end AlgebraicGeometry.ProEtale.CondensedRing
