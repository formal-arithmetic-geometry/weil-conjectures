/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientRefinementExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived

/-! # Normalized exchange comparison for the two finite coefficient models
(blueprint: lem-sp-original-finite-coefficient-exchange-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- Derive the specified underived finite coefficient direct-image comparison.
Both coefficient functors are equivalences, hence exact and preserve K-injectives.
(blueprint: lem-sp-original-finite-coefficient-exchange-comparison) -/
def originalFiniteCoefficientPushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientDerivedLowerStar (Profinite.continuousMapRingObj T) f ⋙
        (finiteCoefficientDerivedEquivalence Y T).functor ≅
      (finiteCoefficientDerivedEquivalence X T).functor ⋙
        R(ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (lowerStar (Profinite.continuousMapRingObj T) f)
      (finiteCoefficientModEquivalence Y T).functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarFiniteCoefficientModEquivalenceIso f T) ≪≫
    Functor.rightDerivedFunctorCompIso (finiteCoefficientModEquivalence X T).functor
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f) ≪≫
    Functor.isoWhiskerRight
      (finiteCoefficientModEquivalence X T).functor.rightDerivedFunctorIsoMapDerivedCategory _

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Fixed source comparison between condensed and ordinary finite coefficient models.
(blueprint: lem-sp-original-finite-coefficient-exchange-comparison) -/
def originalFiniteCoefficientExchangeSource
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))) :
    (finiteCoefficientDerivedEquivalence Y' T).functor.obj
        ((coefficientDerivedUpperStar (Profinite.continuousMapRingObj T) g).obj
          ((coefficientDerivedLowerStar (Profinite.continuousMapRingObj T) f).obj K)) ≅
      (L(ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) g)).obj
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)).obj
          ((finiteCoefficientDerivedEquivalence X T).functor.obj K)) :=
  (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso g T).app
      ((coefficientDerivedLowerStar (Profinite.continuousMapRingObj T) f).obj K) ≪≫
    (L(ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) g)).mapIso
      ((originalFiniteCoefficientPushIso T f).app K)

/-- Fixed target comparison between the same finite coefficient models.
(blueprint: lem-sp-original-finite-coefficient-exchange-comparison) -/
def originalFiniteCoefficientExchangeTarget
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))) :
    (finiteCoefficientDerivedEquivalence Y' T).functor.obj
        ((coefficientDerivedLowerStar (Profinite.continuousMapRingObj T) f').obj
          ((coefficientDerivedUpperStar (Profinite.continuousMapRingObj T) g').obj K)) ≅
      (R(ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f')).obj
        ((L(ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) g')).obj
          ((finiteCoefficientDerivedEquivalence X T).functor.obj K)) :=
  (originalFiniteCoefficientPushIso T f').app
      ((coefficientDerivedUpperStar (Profinite.continuousMapRingObj T) g').obj K) ≪≫
    (R(ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f')).mapIso
      ((leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso g' T).app K)

/-- The finite coefficient equivalence identifies the specified exchange maps, with
endpoint identifications fixed by the published pullback and direct-image comparisons.

Source: Bhatt--Scholze, Proposition 5.3.2 and Section 6.8; adjunction mate calculus.

Proof in words. The underived direct-image comparison is the identity on underlying
abelian sheaves, and the inverse-image comparison is its conjugate under the two geometric
adjunctions. Derive these comparisons through the exact coefficient equivalences. Their
unit and counit equations remain the derived unit and counit equations, since equivalences
preserve injective resolutions and both pullbacks are exact. The underived composition
comparisons commute with this common sectionwise encoding. Deriving that equality and
inserting the exact-pullback identifications gives the square coherence for the published
leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso, including sq.w. Expand both
exchange maps into unit, pullback-square comparison, and counit. The three commuting
squares paste to the equality below with exactly the defined endpoint maps. No properness,
constructibility, or etale-origin assumption is used; this is a comparison of arbitrary
maps before proper base change is applied.
(blueprint: lem-sp-original-finite-coefficient-exchange-comparison) -/
theorem originalFiniteCoefficientExchangeComparison
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))) :
    (finiteCoefficientDerivedEquivalence Y' T).functor.map
        ((refinementAmbientExchange (Profinite.continuousMapRingObj T) sq).app K) ≫
        (originalFiniteCoefficientExchangeTarget T (f' := f') (g' := g') K).hom =
      (originalFiniteCoefficientExchangeSource T (f := f) (g := g) K).hom ≫
        (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} T))
          sq.toCommSq).app ((finiteCoefficientDerivedEquivalence X T).functor.obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
