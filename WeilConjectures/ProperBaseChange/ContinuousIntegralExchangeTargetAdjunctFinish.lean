/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPullComposition
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
import all WeilConjectures.ProperBaseChange.ContinuousIntegralExchangeTargetAdjunctPull

/-! # Coherence of integral localization and the specified exchange map: finishing steps

The base-change adjunct and the target-side normal form used by
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` (split from it for compile time). -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

open CategoryTheory

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

attribute [local irreducible] derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction derivedComapLowerStarIso
  Adjunction.pushHomOfComapIso Adjunction.pullIsoOfComapIso Adjunction.restrictFullyFaithful


section BaseChangeCalculation
attribute [local irreducible] Adjunction.homEquiv
  boundedConstructibleUpperStar UnitBallRingObj.boundedConstructibleLowerStar
  ContinuousMapRingObj.boundedConstructibleLowerStar
  UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction
  ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction
  boundedConstructiblePullbackSquareComparison
private lemma boundedBaseChange_adjunct
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)) :
    ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
      (f'.asOver (Spec (.of k)))).homEquiv
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
          (f.asOver (Spec (.of k)))).obj K))
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj
        K)).symm
      ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
        (sq.asOver (Spec (.of k)))).app K) =
    ((boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ
      (sq.asOver (Spec (.of k)))).app
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
        (f.asOver (Spec (.of k)))).obj K)).hom ≫
        (boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).map
          ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
            (f.asOver (Spec (.of k)))).counit.app K) := by
  rw [Adjunction.homEquiv_counit, Iso.app_hom]
  -- Restate the exchange with the `integralCoeff` functors, so that the kernel only compares
  -- `integralCoeff ℓ E` with its unfolding as arguments of the (unexpanded) operations.
  have h : UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
      (sq.asOver (Spec (.of k))) = Adjunction.squareExchange
        (UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
          (f.asOver (Spec (.of k))))
        (UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
          (f'.asOver (Spec (.of k))))
        (boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k))))
        (boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k))))
        (boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ
          (sq.asOver (Spec (.of k)))) :=
    UnitBallRingObj.boundedConstructibleBaseChange_eq_squareExchange ℓ (continuousIntegers ℓ E)
      (sq.asOver (Spec (.of k)))
  exact Adjunction.squareExchange_map_counit_of_eq _ _ _ _ _ h K

end BaseChangeCalculation

section AdjunctCalculation

-- Use the adjunction API without reducing the chosen derived adjunctions.
attribute [local irreducible] integralScalarConstructible integralConstructiblePullIso
attribute [local irreducible] Adjunction.homEquiv
  boundedConstructibleUpperStar UnitBallRingObj.boundedConstructibleLowerStar
  UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction

private lemma integral_counit_pull_naturality
    (K : integralConstructible ℓ E X) :
    scalarMap (integralScalarConstructible ℓ E X')
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).map
          ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
            (.of k)))).counit.app K)) ≫
      integralConstructiblePullHom ℓ E k g' K =
    integralConstructiblePullHom ℓ E k g'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)) ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        (scalarMap (integralScalarConstructible ℓ E X)
          ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
            (.of k)))).counit.app K)) := by
  exact integralPull_naturality ℓ E k g'
    (K := (boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K))
    (L := K)
    ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of
      k)))).counit.app K)

private lemma finish_step1
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K))).inv ≫
      scalarMap (integralScalarConstructible ℓ E X')
        (((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f'.asOver (Spec
          (.of k)))).homEquiv
            ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
              ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
                K))
            ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj
              K)).symm
          ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E) (sq.asOver (Spec (.of k)))).app K))
            ≫
      integralConstructiblePullHom ℓ E k g' K =
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K))).inv ≫
    scalarMap (integralScalarConstructible ℓ E X')
      (((boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of
        k)))).app
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K)).hom) ≫
    scalarMap (integralScalarConstructible ℓ E X')
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).map
        ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
          (.of k)))).counit.app K)) ≫
    integralConstructiblePullHom ℓ E k g' K := by
  exact map_eq_whisker (integralScalarConstructible ℓ E X')
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K))).inv
    (integralConstructiblePullHom ℓ E k g' K) _ _ _
    (boundedBaseChange_adjunct ℓ E k f g f' g' sq K)

private lemma finish_step2
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K))).inv ≫
    scalarMap (integralScalarConstructible ℓ E X')
      (((boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of
        k)))).app
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K)).hom) ≫
    scalarMap (integralScalarConstructible ℓ E X')
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).map
        ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
          (.of k)))).counit.app K)) ≫
    integralConstructiblePullHom ℓ E k g' K =
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K))).inv ≫
    scalarMap (integralScalarConstructible ℓ E X')
      (((boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of
        k)))).app
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K)).hom) ≫
    integralConstructiblePullHom ℓ E k g'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)) ≫
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
      k)))).map
      (scalarMap (integralScalarConstructible ℓ E X)
        ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
          (.of k)))).counit.app K)) := by
  conv_lhs =>
    rhs
    rhs
    rw [integral_counit_pull_naturality ℓ E k f g' K]

private lemma finish_step3
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K))).inv ≫
    scalarMap (integralScalarConstructible ℓ E X')
      (((boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of
        k)))).app
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K)).hom) ≫
    integralConstructiblePullHom ℓ E k g'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)) ≫
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
      k)))).map
      (scalarMap (integralScalarConstructible ℓ E X)
        ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
          (.of k)))).counit.app K)) =
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of
      k)))).map
        (integralConstructiblePullHom ℓ E k g
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)) ≫
      ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ (sq.asOver
        (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E Y).obj
            ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
              K))).hom ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        (integralConstructiblePullIso ℓ E k f
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
            K)).inv ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        (scalarMap (integralScalarConstructible ℓ E X)
          ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
            (.of k)))).counit.app K)) := by
  simpa only [Category.assoc] using congrArg
    (fun v ↦ v ≫ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver
      (Spec (.of k)))).map
      (scalarMap (integralScalarConstructible ℓ E X)
        ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
          (.of k)))).counit.app K)))
    (integralPull_square ℓ E k f g f' g' sq
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K))

private lemma integral_target_finish
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
          K))).inv ≫
      scalarMap (integralScalarConstructible ℓ E X')
        (((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f'.asOver (Spec
          (.of k)))).homEquiv
            ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
              ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
                K))
            ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj
              K)).symm
          ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E) (sq.asOver (Spec (.of k)))).app K))
            ≫
      integralConstructiblePullHom ℓ E k g' K =
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of
      k)))).map
        (integralConstructiblePullHom ℓ E k g
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)) ≫
      ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ (sq.asOver
        (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E Y).obj
            ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
              K))).hom ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        (integralConstructiblePullIso ℓ E k f
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
            K)).inv ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        (scalarMap (integralScalarConstructible ℓ E X)
          ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
            (.of k)))).counit.app K)) := by
  exact (finish_step1 ℓ E k f g f' g' sq K).trans
    ((finish_step2 ℓ E k f g f' g' sq K).trans
      (finish_step3 ℓ E k f g f' g' sq K))

end AdjunctCalculation

end General

end AlgebraicGeometry.ProEtale.CondensedRing
