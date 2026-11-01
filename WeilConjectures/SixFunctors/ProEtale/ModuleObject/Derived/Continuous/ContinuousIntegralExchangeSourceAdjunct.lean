/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import all WeilConjectures.ProperBaseChange.ContinuousIntegralExchangeSourceAdjunctCounit

/-! # Coherence of integral localization and the specified exchange map -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

private lemma source_normal_form
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (θ : G ⋙ L' ≅ L ⋙ H) (β : R ⋙ G ⟶ H ⋙ R')
    (N : D) (M : C) (A : C') (s : A ⟶ G.obj M) (δ : M ⟶ R.obj N)
    (Q : D) (q : L.obj M ⟶ Q) (r : Q ⟶ N)
    (hβ : β = Adjunction.squareExchange a b G H θ)
    (hc : L.map δ ≫ a.counit.app N = q ≫ r) :
    (b.homEquiv A (H.obj N)).symm ((s ≫ G.map δ) ≫ β.app N) =
      L'.map s ≫ θ.hom.app M ≫ H.map q ≫ H.map r := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit,
    Adjunction.squareExchange_map_counit_of_eq a b G H θ hβ N]
  simp only [Functor.map_comp, Category.assoc]
  have hn := θ.hom.naturality δ
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [← H.map_comp, hc, H.map_comp]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
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

/-- Normal form for the source side after the bounded f′ adjunction.
Source: Bhatt--Scholze, Remark 6.8.15; ChangeOfCoefficients.lean derived comparisons
and the specified unit-square-counit exchange construction.
(blueprint: lem-weil-pbc-continuous-integral-exchange-source-adjunct).

Proof. Apply the bounded f′ adjunction to the source composite. Expand functoriality, then
replace the exchange adjunct by square transport followed by the f counit. Naturality of the
square comparison moves the f push comparison past it. The iterated mate/conjugation identity
identifies pullback of that push comparison followed by the E counit with the inverse pull
comparison followed by scalar extension of the integral counit. These substitutions give exactly
the displayed composite. -/
theorem integralConstructible_exchange_source_adjunct
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f'.asOver (Spec (.of k)))).homEquiv _ _).symm
      (integralConstructibleSourceHom ℓ E k f g K ≫
        (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
          (sq.asOver (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E X).obj K)) =
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (f'.asOver (Spec (.of k)))).map
        (integralConstructiblePullHom ℓ E k g
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)) ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
        (sq.asOver (Spec (.of k)))).hom.app
          ((integralScalarConstructible ℓ E Y).obj
            ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
              (f.asOver (Spec (.of k)))).obj K)) ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (g'.asOver (Spec (.of k)))).map
        (integralConstructiblePullIso ℓ E k f
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
            (f.asOver (Spec (.of k)))).obj K)).inv ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (g'.asOver (Spec (.of k)))).map
        ((integralScalarConstructible ℓ E X).map
          ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
            (f.asOver (Spec (.of k)))).counit.app K)) := by
  exact source_normal_form
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f.asOver (Spec (.of k))))
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f'.asOver (Spec (.of k))))
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k))))
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k))))
    (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
      (sq.asOver (Spec (.of k))))
    (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E (sq.asOver (Spec (.of k))))
    ((integralScalarConstructible ℓ E X).obj K)
    ((integralScalarConstructible ℓ E Y).obj
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K))
    ((integralScalarConstructible ℓ E Y').obj
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)))
    (integralConstructiblePullHom ℓ E k g
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K))
    (integralConstructiblePushHom ℓ E k f K)
    ((integralScalarConstructible ℓ E X).obj
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)))
    (integralConstructiblePullIso ℓ E k f
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)).inv
    ((integralScalarConstructible ℓ E X).map
      ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
        (f.asOver (Spec (.of k)))).counit.app K))
    (ContinuousMapRingObj.boundedConstructibleBaseChange_eq_squareExchange ℓ E
      (sq.asOver (Spec (.of k))))
    (integral_push_counit ℓ E k f K)

end AlgebraicGeometry.ProEtale.CondensedRing

-- The concrete identity's inferred instances make Lean's two premise-index export passes
-- expensive. Its name is used explicitly by `ContinuousIntegralExchangeEquality`; exclude just
-- this identity from suggestions using Lean's documented API.
run_cmd do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "integralConstructible_exchange_source_adjunct"
