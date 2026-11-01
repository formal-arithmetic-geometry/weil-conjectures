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
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import all WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
import all WeilConjectures.ProperBaseChange.ContinuousIntegralExchangeTargetAdjunctPull
import all WeilConjectures.ProperBaseChange.ContinuousIntegralExchangeTargetAdjunctFinish
import all WeilConjectures.ProperBaseChange.ContinuousIntegralExchangeTargetAdjunctCounit

/-! # Coherence of integral localization and the specified exchange map -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

open CategoryTheory

-- The diagram lemmas stay here too: `CondensedQbarPullbackCube` uses them through `import all`.
section Diagrams
universe v₅ u₅
variable {C : Type u₅} [Category.{v₅} C]
private lemma rectangle
    {A₀ A₁ A₂ A₃ B₀ B₁ C₀ C₁ D₀ D₁ : C}
    (p : A₀ ≅ A₁) (q : A₃ ≅ A₂) (r : A₀ ≅ A₃)
    (pE : C₁ ≅ C₀) (qE : D₁ ≅ D₀) (rE : C₁ ≅ D₁)
    (a : A₁ ⟶ B₀) (b : B₀ ⟶ C₀) (c : A₂ ⟶ B₁) (d : B₁ ⟶ D₀)
    (e : A₀ ⟶ C₁) (f : A₃ ⟶ D₁)
    (h₁ : q.hom ≫ c ≫ d = f ≫ qE.hom)
    (h₂ : p.hom ≫ a ≫ b = e ≫ pE.hom)
    (he : r.hom ≫ f = e ≫ rE.hom) :
    p.inv ≫ r.hom ≫ q.hom ≫ c ≫ d = a ≫ b ≫ pE.inv ≫ rE.hom ≫ qE.hom := by
  apply (cancel_epi p.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [h₁, reassoc_of% he, reassoc_of% h₂]
  simp
universe u₆ v₆
private lemma mapped_rectangle {D : Type u₆} [Category.{v₆} D]
    (F : C ⥤ D) {A₀ A₁ A₂ A₃ : C} {B₀ B₁ C₀ C₁ D₀ D₁ : D}
    (p : A₀ ≅ A₁) (q : A₃ ≅ A₂) (r : A₀ ≅ A₃)
    (pE : C₁ ≅ C₀) (qE : D₁ ≅ D₀) (rE : C₁ ≅ D₁)
    (a : F.obj A₁ ⟶ B₀) (b : B₀ ⟶ C₀)
    (c : F.obj A₂ ⟶ B₁) (d : B₁ ⟶ D₀)
    (e : F.obj A₀ ⟶ C₁) (f : F.obj A₃ ⟶ D₁)
    (h₁ : F.map q.hom ≫ c ≫ d = f ≫ qE.hom)
    (h₂ : F.map p.hom ≫ a ≫ b = e ≫ pE.hom)
    (he : F.map r.hom ≫ f = e ≫ rE.hom) :
    F.map (p.inv ≫ r.hom ≫ q.hom) ≫ c ≫ d =
      a ≫ b ≫ pE.inv ≫ rE.hom ≫ qE.hom := by
  simpa only [CategoryTheory.Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc] using
    rectangle (F.mapIso p) (F.mapIso q) (F.mapIso r) pE qE rE a b c d e f h₁ h₂ he

private lemma mapped_iso_rectangle {D : Type u₆} [Category.{v₆} D]
    (F : C ⥤ D) {A₀ A₁ A₂ A₃ : C} {B₀ B₁ C₀ C₁ D₀ D₁ : D}
    (p : A₀ ≅ A₁) (q : A₃ ≅ A₂) (r : A₀ ≅ A₃)
    (pE : C₁ ≅ C₀) (qE : D₁ ≅ D₀) (rE : C₁ ≅ D₁)
    (a : F.obj A₁ ≅ B₀) (b : B₀ ≅ C₀)
    (c : F.obj A₂ ≅ B₁) (d : B₁ ≅ D₀)
    (e : F.obj A₀ ≅ C₁) (f : F.obj A₃ ≅ D₁)
    (h₁ : F.mapIso q ≪≫ c ≪≫ d = f ≪≫ qE)
    (h₂ : F.mapIso p ≪≫ a ≪≫ b = e ≪≫ pE)
    (he : F.mapIso r ≪≫ f = e ≪≫ rE) :
    F.mapIso (p.symm ≪≫ r ≪≫ q) ≪≫ c ≪≫ d =
      a ≪≫ b ≪≫ pE.symm ≪≫ rE ≪≫ qE := by
  apply Iso.ext
  exact mapped_rectangle F p q r pE qE rE a.hom b.hom c.hom d.hom e.hom f.hom
    (congrArg Iso.hom h₁) (congrArg Iso.hom h₂) (congrArg Iso.hom he)

private lemma inverse_square {P Q R S : C}
    (a : P ≅ Q) (b : R ≅ S) (x : P ⟶ R) (u : Q ⟶ S)
    (h : x ≫ b.hom = a.hom ≫ u) : a.inv ≫ x = u ≫ b.inv := by
  apply (cancel_mono b.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using congrArg (fun v ↦ a.inv ≫ v) h
private lemma inverse_mapped_square {D : Type u₆} [Category.{v₆} D]
    (F : D ⥤ C) {P Q R : C} {S T : D}
    (a : P ≅ Q) (b : S ≅ T) (x : P ⟶ R) (y : R ⟶ F.obj S)
    (u : Q ⟶ F.obj T)
    (h : x ≫ y ≫ F.map b.hom = a.hom ≫ u) :
    a.inv ≫ x ≫ y = u ≫ F.map b.inv := by
  simpa only [Category.assoc, Functor.mapIso_inv] using
    inverse_square a (F.mapIso b) (x ≫ y) u
      (by simpa only [Category.assoc, Functor.mapIso_hom] using h)

end Diagrams

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section FiniteIntermediateField

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

-- Use the adjunction API without reducing the chosen derived adjunctions.
attribute [local irreducible] integralScalarConstructible integralConstructiblePullIso
attribute [local irreducible] Adjunction.homEquiv
  boundedConstructibleUpperStar UnitBallRingObj.boundedConstructibleLowerStar
  UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction
attribute [local irreducible] ContinuousMapRingObj.boundedConstructibleLowerStar
  ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction

private lemma integral_target_start
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f'.asOver (Spec (.of k)))).homEquiv _ _).symm
      (scalarMap (integralScalarConstructible ℓ E Y')
          ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E) (sq.asOver (Spec (.of k)))).app K)
            ≫
        integralConstructibleTargetHom ℓ E k f' g' K) =
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
      integralConstructiblePullHom ℓ E k g' K := by
  exact adjunct_target_start
    (UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f'.asOver (Spec (.of
      k))))
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f'.asOver (Spec (.of k))))
    ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E) (sq.asOver (Spec (.of k)))).app K)
    (integralConstructiblePushHom ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj K))
    (integralConstructiblePullHom ℓ E k g' K)
    (integralConstructibleTargetHom ℓ E k f' g' K) rfl
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)))
    (integralConstructiblePullIso ℓ E k f'
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f'.asOver (Spec (.of k)))).obj
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj K)))
    (integralPull_counit ℓ E k f' _)
    (integralPull_inv_naturality ℓ E k f' _)

/-- Normal form for the target side after the bounded f′ adjunction.
Source: Bhatt--Scholze, Remark 6.8.15; ChangeOfCoefficients.lean derived comparisons
and the specified unit-square-counit exchange construction.
(blueprint: lem-weil-pbc-continuous-integral-exchange-target-adjunct).

Proof. Apply the bounded f′ adjunction to the target composite. Counit naturality moves the g′
pull comparison past the f′ counit. The mate/counit identity replaces the f′ push comparison.
Naturality of the inverse f′ pull comparison moves scalar extension of integral exchange past
it. Expand the integral exchange adjunct and use naturality of the g′ pull comparison. Coherence
of the specified pull comparisons with composition, obtained by right deriving the
restriction/pushforward composition diagram and conjugating through adjunctions, gives the pull
square cube. Precompose that cube with inverse f′ pull comparison and postcompose with g′
pullback of inverse f pull comparison. Cancel these two isomorphisms and postcompose with scalar
extension of the integral counit. This is the displayed composite. No push comparison or
exchange is inverted. -/
theorem integralConstructible_exchange_target_adjunct
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f'.asOver (Spec (.of k)))).homEquiv _ _).symm
      ((integralScalarConstructible ℓ E Y').map
          ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E) (sq.asOver (Spec (.of k)))).app K)
            ≫
        integralConstructibleTargetHom ℓ E k f' g' K) =
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of
      k)))).map
        (integralConstructiblePullHom ℓ E k g
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K)) ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ (sq.asOver
        (Spec (.of k)))).hom.app
          ((integralScalarConstructible ℓ E Y).obj
            ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj K))
              ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        (integralConstructiblePullIso ℓ E k f
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).obj
            K)).inv ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        ((integralScalarConstructible ℓ E X).map
          ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E) (f.asOver (Spec
            (.of k)))).counit.app K)) := by
  -- The square comparison of the statement is taken with the subtype topology on `E`, the
  -- calculation produces it with the normed field topology. They agree definitionally; compare
  -- them as arguments of the comparison, so that the kernel never unfolds the comparison itself.
  have e : boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
      (sq.asOver (Spec (.of k))) =
      boundedConstructiblePullbackSquareComparison (normedRing E) ℓ (sq.asOver (Spec (.of k))) :=
    rfl
  have hθ := congrArg (fun x ↦ (x.app ((integralScalarConstructible ℓ E Y).obj
    ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
      (f.asOver (Spec (.of k)))).obj K))).hom) e
  exact ((integral_target_start ℓ E k f g f' g' sq K).trans
    (integral_target_finish ℓ E k f g f' g' sq K)).trans
      (congrArg (fun t ↦
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (f'.asOver (Spec (.of k)))).map
            (integralConstructiblePullHom ℓ E k g
              ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
                (f.asOver (Spec (.of k)))).obj K)) ≫ t ≫
          (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (g'.asOver (Spec (.of k)))).map
            (integralConstructiblePullIso ℓ E k f
              ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
                (f.asOver (Spec (.of k)))).obj K)).inv ≫
          (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (g'.asOver (Spec (.of k)))).map
            ((integralScalarConstructible ℓ E X).map
              ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ
                (continuousIntegers ℓ E) (f.asOver (Spec (.of k)))).counit.app K))) hθ.symm)

end FiniteIntermediateField

end AlgebraicGeometry.ProEtale.CondensedRing

-- The concrete identity's inferred instances make Lean's two premise-index export passes
-- expensive. Its name is used explicitly by `ContinuousIntegralExchangeEquality`; exclude just
-- this identity from suggestions using Lean's documented API.
run_cmd do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "integralConstructible_exchange_target_adjunct"
