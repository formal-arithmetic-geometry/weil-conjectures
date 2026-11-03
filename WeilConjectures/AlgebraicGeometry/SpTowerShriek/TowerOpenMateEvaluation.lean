/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization

/-!
# Evaluation of the open base-change mate on varying-coefficient towers

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/
sk-lem-sp-tower-bound/sk-lem-sp-tower-bound-operations.proof.md, (2) and (3).
(blueprint: lem-sp-strict-open-word-evaluation).

All operations below use the existing section-normalized sequence-site coordinates.
The index n denotes the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual natural left mate, constructed before any invertibility assertion.
Its component is the transpose defining `openMate`.
Source: blueprint operations proof (2)
(blueprint: lem-sp-strict-open-word-evaluation). -/
def towerOpenAlpha (b : Base l E) (o : Operations l E b)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : h ≫ j = j' ≫ g) :
    pull l E b (o.geometry h) ⋙ openD l E b (o.openOp j') ⟶
      openD l E b (o.openOp j) ⋙ pull l E b (o.geometry g) :=
  ((mateEquiv (o.openOp j).derivedAdjunction (o.openOp j').derivedAdjunction).symm
    (TwoSquare.mk _ _ _ _ (square l E b o h j' j g w).inv)).natTrans

/-- The canonical finite open comparison, in the existing intrinsic constant-ring
coordinates. The middle arrow is the inverse of the ordinary finite open mate,
transported through the canonical module realization. Localization is termwise;
the outer comparisons are the unit-preserving tensor-pullback identifications.
Source: blueprint operations proof (2); finite open-extension base change
(blueprint: lem-sp-strict-open-word-evaluation). -/
def towerOpenFiniteBeta (b : Base l E)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ) :
    sfIntrinsicDerivedOpen (R l E n) j ⋙
        proEtaleConstantRingDerivedPullback (R l E n) g ≅
      proEtaleConstantRingDerivedPullback (R l E n) h ⋙
        sfIntrinsicDerivedOpen (R l E n) j' := by
  letI := sfIntrinsicPullback_additive (R l E n) h
  letI := sfIntrinsicPullback_additive (R l E n) g
  letI := sfIntrinsicExtensionByZero_additive j (R l E n)
  letI := sfIntrinsicExtensionByZero_additive j' (R l E n)
  let ordinary :
      sfIntrinsicExtensionByZero j (R l E n) ⋙ sfIntrinsicPullback (R l E n) g ≅
        sfIntrinsicPullback (R l E n) h ⋙ sfIntrinsicExtensionByZero j' (R l E n) :=
    (sfIntrinsicTransportComp (R l E n)
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) g)).symm ≪≫
    sfIntrinsicTransportIso (R l E n)
      (ProEtale.openImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq).symm ≪≫
    sfIntrinsicTransportComp (R l E n)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) h)
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j')
  exact
    Functor.isoWhiskerLeft (sfIntrinsicDerivedOpen (R l E n) j)
      (openSquareDerivedPullbackModel (R l E n) g) ≪≫
    (Functor.mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero j (R l E n))
      (sfIntrinsicPullback (R l E n) g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso ordinary ≪≫
    Functor.mapDerivedCategoryCompIso (sfIntrinsicPullback (R l E n) h)
      (sfIntrinsicExtensionByZero j' (R l E n)) ≪≫
    Functor.isoWhiskerRight (openSquareDerivedPullbackModel (R l E n) h).symm
      (sfIntrinsicDerivedOpen (R l E n) j')

/-- Evaluation of the source of the left mate, retaining both canonical comparisons.
Source: blueprint operations proof (2)
(blueprint: lem-sp-strict-open-word-evaluation). -/
def towerOpenSourceEvaluation (b : Base l E) (o : Operations l E b)
    {U' U T' : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T') [IsOpenImmersion j']
    (n : ℕ) :
    (pull l E b (o.geometry h) ⋙ openD l E b (o.openOp j')) ⋙ Ev l E T' n ≅
      Ev l E U n ⋙ (proEtaleConstantRingDerivedPullback (R l E n) h ⋙
        sfIntrinsicDerivedOpen (R l E n) j') :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (openEvaluation l E b (o.openOp j') n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((o.geometry h).pullEvaluation n) _ ≪≫
    Functor.associator _ _ _

/-- Evaluation of the target of the left mate, retaining both canonical comparisons.
Source: blueprint operations proof (2)
(blueprint: lem-sp-strict-open-word-evaluation). -/
def towerOpenTargetEvaluation (b : Base l E) (o : Operations l E b)
    {U T' T : Scheme.{u}} (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j]
    (n : ℕ) :
    (openD l E b (o.openOp j) ⋙ pull l E b (o.geometry g)) ⋙ Ev l E T' n ≅
      Ev l E U n ⋙ (sfIntrinsicDerivedOpen (R l E n) j ⋙
        proEtaleConstantRingDerivedPullback (R l E n) g) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((o.geometry g).pullEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openEvaluation l E b (o.openOp j) n) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtale.SpTowerShriek
