/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.SchemeGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedEquivalence
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower
public import WeilConjectures.AlgebraicGeometry.IntegralAdjunctionBijection
public import WeilConjectures.AlgebraicGeometry.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.PurityCompactSupportTransport
public import WeilConjectures.AlgebraicGeometry.PurityTateDatum
public import WeilConjectures.AlgebraicGeometry.PurCompletedReindexingData
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.AlgebraicGeometry.ProperIntegralOrdinaryData
public import WeilConjectures.AlgebraicGeometry.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.CompletedExtensionZeroComparison

/-! # Integral realization of the geometric comparison diagram

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-bijection.md,
Normalization, Bijections and Purity; geometric-equivariance proof, Step 5
(blueprint: lem-pur-integral-geometric-comparison-realization).

The comparison equations concern morphisms of entire strict systems. The positive
ell-power exponent n+1 is indexed by n. Scalar restriction precedes total derived limit.

## Main definitions

- `PullLimit` and `PreservesKInjectives`: normalized geometric pullback and total limit.
- `SourceModel` and `TateComparison`: the actual pullback, tensor, shift and Tate word.
- `CoefficientTransport` and `CompletedExchange`: the specified completed support exchange.
- `Diagram` and `Result`: realization of the entire geometric comparison diagram.

## Main statements

- `integral_geometric_comparison_realization`: existence under the standing finite-field setting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralGeometricComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The K-injective clause refers to the actual completed module pullback and to
its strict fixed-ring tower functor, before localization. Evaluation or scalar
restriction is not claimed to preserve K-injectives.
Source: integral geometric realization, inverse-image-equivalence paragraph
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def PreservesKInjectives {T' T : Scheme.{u}} (g : T' ⟶ T) : Prop :=
  (∀ I : CochainComplex
      (reductionModules T ((pbcIntegralDatum l E).completedRing T)) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      (((proEtaleRingModulePullback g ((pbcIntegralDatum l E).completedRing T)
        ((pbcIntegralDatum l E).completedRing T')
        ((pbcIntegralDatum l E).integralRingIso g)).mapHomologicalComplex (.up ℤ)).obj I)) ∧
  (∀ I : CochainComplex ((pbcIntegralDatum l E).towers T) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      ((((pbcIntegralDatum l E).towerModulePull g).mapHomologicalComplex (.up ℤ)).obj I))

variable (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Pullback commutes with total limit on the actual normalized constructible
towers. The displayed equation fixes its value on reconstructed objects by the
reconstruction units and the whole-system pullback comparison.
Source: integral geometric realization, first displayed pair and its unit clause
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
structure PullLimit {T' T : Scheme.{u}} (g : T' ⟶ T)
    [∀ x : T, Invertible (l : T.residueField x)]
    [∀ x : T', Invertible (l : T'.residueField x)]
    (r' : SpExceptionalBaseChange.IntegralCoordinates l E b q T')
    (r : SpExceptionalBaseChange.IntegralCoordinates l E b q T)
    (m : SpExceptionalBaseChange.PullModel l E b o q g r' r) where
  comparison :
    (spNormalizedConstructibleTorTowers l E T (q.abelian T)).ι ⋙
        SpExceptionalBaseChange.lim l E b q r ⋙ integralDerivedPullback l E g ≅
      (spNormalizedConstructibleTorTowers l E T (q.abelian T)).ι ⋙
        SpTowerCalculus.etalePullback l E b o q g ⋙
          SpExceptionalBaseChange.lim l E b q r'
  unit : ∀ K : sfIntegralConstructibleCategory l E T,
    r'.normalization.adjunction.unit.app
        ((constructibleIntegralPullback l E g).obj K).obj ≫
      (SpExceptionalBaseChange.lim l E b q r').map
        (SpExceptionalBaseChange.pullReduction l E b o q g r' r m K) =
    (integralDerivedPullback l E g).map
        (r.normalization.adjunction.unit.app K.obj) ≫
      comparison.hom.app
        ⟨((SpExceptionalBaseChange.red l E b q r).obj K).obj,
          ⟨r.closed K, r.normalized K⟩⟩

/-- The signed Tate line, pullback, tensor and even shift on entire strict towers.
The line is the simultaneous reduction of the actual integral roots-of-unity
line, rather than independently chosen finite derived objects.
Source: integral geometric realization, H_bullet and the canonical Tate factor
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def towerSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    (rX : SpExceptionalBaseChange.IntegralCoordinates l E b q X) (d : ℕ) :
    SpTowerCalculus.C l E b q Y ⥤ SpTowerShriek.D l E X :=
  SpTowerGamma.realization l E b q Y ⋙ SpTowerShriek.pull l E b (o.geometry f) ⋙
    Prod.sectL (SpTowerShriek.D l E X)
      (SpTwistedPullback.line l E b X (q.abelian X) rX.reduction (d : ℤ)) ⋙
        SpTowerShriek.tensor l E b X ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- The normalized comparison from completed pullback/tensor/shift to that
entire strict word. Its constituent comparisons are specified before localization:
cofinal pullback is the mate of the identity on sections, tensor is fixed on all
pure total-complex summands, and reduction uses the actual quotient units.
Source: integral geometric realization, proof Steps 2, 6 and 7
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
structure SourceModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (rX : SpExceptionalBaseChange.IntegralCoordinates l E b q X)
    (rY : SpExceptionalBaseChange.IntegralCoordinates l E b q Y) (d : ℕ) where
  geometry : SpTwistedPullback.CofinalGeometry l E b f (o.geometry f) rX.cofinal rY.cofinal
  tensor : SpTwistedPullback.CofinalTensor l E b X rX.cofinal
  shift : PurReductionLimitShiftData l E X
    (coefficientDerivedSystemEvaluationCalculus l E X).choose
  tate : SpTwistedPullback.TateReduction l E X
  nativePull : (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f ⋙
      (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ≅
    integralSystemReduction l E Y ⋙ finiteSystemDerivedPullback
      (integralSystemRings l E) (integralSystemTransition l E) f
  native_pull_normalization : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (nativePull.hom.app K)
      ((pullbackTensorCalculus l E X).reduction.map
          ((pullbackTensorIntegralPullbackModel l E f).hom.app K.obj) ≫
        (pullbackTensorCalculus l E X).adjunction.counit.app
          ((pullbackTensorSequenceDerived l E f).obj
            ((pullbackTensorCalculus l E Y).reduction.obj K.obj)))
  comparison : SpTwistedPullback.source l E f (d : ℤ) (2 * (d : ℤ)) ⋙
      SpTwistedPullback.reduction l E b X (q.abelian X) rX.reduction ≅
    SpExceptionalBaseChange.red l E b q rY ⋙ towerSource l E b o q f rX d
  normalization : ∀ K : sfIntegralConstructibleCategory l E Y,
    comparison.app K =
      (rX.cofinalReduction.derived.app
        ((SpTwistedPullback.source l E f (d : ℤ) (2 * (d : ℤ))).obj K)).symm ≪≫
      rX.cofinal.ordinary.mapDerivedCategory.mapIso
        (SpTwistedPullback.nativeComparison l E f (d : ℤ) (2 * (d : ℤ)) shift
          nativePull K) ≪≫
      SpTwistedPullback.cofinalSourceComparison l E b f (o.geometry f)
        (q.abelian X) rX.reduction (q.abelian Y) rY.reduction rX.strict rY.strict
        rX.cofinal rY.cofinal rX.cofinalReduction rY.cofinalReduction geometry tensor
        (d : ℤ) (2 * (d : ℤ)) K


/-- The completed coefficient datum in the universe of the small pro-etale site.
Source: integral geometric realization, R_T and completed exchange
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def detailedCoefficients : PurCompactSupport.Coefficients.{u} where
  ring T := (pbcIntegralDatum l E).completedRing T
  pull g := (pbcIntegralDatum l E).integralRingIso g

/-- Coefficient transport is normalized on quotient projections, tensor-unit
sections and the ordinary-to-completed augmentation. The support comparison is
exactly the scalar-restriction proper/open mate, before any tower evaluation.
Source: integral geometric realization, proof Steps 2, 4 and 8
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
structure CoefficientTransport where
  change : PurCompactSupport.Change (detailedCoefficients l E) (PurCompactSupport.completed l E)
  coefficients : ∀ T : Scheme.{u},
    (adicLisseForget T).map (change.map T) =
        (integralDetailedCoefficientComparison T l E).hom
  support : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f),
    CompleteCompactificationLimit.image l E c ⋙ integralDetailedTransport Y l E ≅
      integralDetailedTransport X l E ⋙ cbcSupport (pbcIntegralDatum l E) c
  support_normalization : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f),
    HEq (support c) (PurCompactSupport.restriction change c).symm
  ordinary : ∀ {T' T : Scheme.{u}} (g : T' ⟶ T),
    PbcProperIntegralPullbackIdentification l E g
  pull : ∀ {T' T : Scheme.{u}} (g : T' ⟶ T) [IsIso g]
      [∀ x : T, Invertible (l : T.residueField x)]
      [∀ x : T', Invertible (l : T'.residueField x)],
    constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E T').ι ⋙
        integralDetailedTransport T' l E ≅
      (sfIntegralConstructible l E T).ι ⋙ integralDetailedTransport T l E ⋙
        (pbcIntegralDatum l E).completedPull g
  pull_normalization : ∀ {T' T : Scheme.{u}} (g : T' ⟶ T) [IsIso g]
      [∀ x : T, Invertible (l : T.residueField x)]
      [∀ x : T', Invertible (l : T'.residueField x)]
      (K : sfIntegralConstructibleCategory l E T),
    (integralDetailedTransport T' l E).map
        ((ordinaryIntegralCompletionComparison l E g).app K.obj) ≫
      (pull g).hom.app K =
    (ordinary g).derivedIso.hom.app K.obj ≫
      (cbcDatumOrdinaryTransport (pbcIntegralDatum l E) g).hom.app
        ((integralDetailedTransport T l E).obj K.obj) ≫
      (pbcIntegralDatum l E).ordinaryToCompleted g
        ((integralDetailedTransport T l E).obj K.obj)

section Square
variable {X' X Y' Y : Scheme.{u}} {gx : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {gy : Y' ⟶ Y} {sq : IsPullback gx f' f gy}
  {c : Compactification f}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
  (a : SpTowerMate.Data l E b o q sq c)
  (s : SpExceptionalBaseChange.IntegralData l E b o q a)
  [QuasiCompact f] [QuasiCompact f']

/-- The roots-of-unity factor on the whole reduced line. The counit of the
section realization and the specified completed-pullback reduction identify its
source. Its remaining factor is the inverse limit of the actual root maps.
Source: integral geometric realization, canonical Tate comparison, Step 7
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def towerTate [IsIso gx] (d : ℕ) :
    (SpTowerShriek.pull l E b (o.geometry gx)).obj
        (SpTwistedPullback.line l E b X (q.abelian X) s.rX.reduction (d : ℤ)) ≅
      SpTwistedPullback.line l E b X' (q.abelian X') s.rX'.reduction (d : ℤ) :=
  ((SpTowerCalculus.realization l E b X' (q.abelian X')).counitIso.app _).symm ≪≫
    (SpTowerCalculus.realization l E b X' (q.abelian X')).functor.mapIso
      ((SpTowerCalculus.inclusion l E b q X').mapIso
        ((s.pullComparison.app (sfIntegralTwistingCoefficient l E X (d : ℤ))).symm ≪≫
          (SpExceptionalBaseChange.red l E b q s.rX').mapIso
            (ObjectProperty.isoMk (sfIntegralConstructible l E X')
              (X := (constructibleIntegralPullback l E gx).obj
                (sfIntegralTwistingCoefficient l E X (d : ℤ)))
              (Y := sfIntegralTwistingCoefficient l E X' (d : ℤ))
              (FrobeniusCoefficientTwists.integralDerivedLineMap l E gx (d : ℤ)))))

/-- The ordered whole-tower pullback/tensor/shift word. The square comparison is
that of the actual scheme square; the line comparison is towerTate above.
Source: integral geometric realization, b_bullet and Step 7
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def towerTateWord [IsIso gx] (d : ℕ) (K : SpTowerCalculus.C l E b q Y) :
    (SpTowerShriek.pull l E b (o.geometry gx)).obj
        ((towerSource l E b o q f s.rX d).obj K) ≅
      (towerSource l E b o q f' s.rX' d).obj ((SpTowerMate.V l E b o q a).obj K) :=
  ((SpTowerShriek.pull l E b (o.geometry gx)).commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor (SpTowerShriek.D l E X') (2 * (d : ℤ))).mapIso
      (((o.geometry gx).tensorPullback.app
        ((SpTowerShriek.pull l E b (o.geometry f)).obj
          ((SpTowerGamma.realization l E b q Y).obj K),
          SpTwistedPullback.line l E b X (q.abelian X) s.rX.reduction (d : ℤ))) ≪≫
        (SpTowerShriek.tensor l E b X').mapIso
          (Iso.prod
            (((SpTowerShriek.square l E b o gx f' f gy sq.w).app
              ((SpTowerGamma.realization l E b q Y).obj K)).symm ≪≫
              (SpTowerShriek.pull l E b (o.geometry f')).mapIso
                ((SpTowerCalculus.realization l E b Y'
                  (q.abelian Y')).counitIso.app _).symm)
            (towerTate l E b o q a s d)))

/-- The completed exchange is the realization of the tower exchange, with
coefficient transport by the canonical proper/open scalar mates. The equation
uses the actual completedCompactSupportExchange for every generating tuple of
the adic ideal, so includes all permitted presentations of completeness.
Source: integral geometric realization, B = Ex!comp, Step 8
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
structure CompletedExchange [IsIso gx] [IsIso gy]
    (t : CoefficientTransport l E)
    (beta : SpIntegralAdjunction.support l E c s.support_closed ⋙
        constructibleIntegralPullback l E gy ≅
      constructibleIntegralPullback l E gx ⋙
        SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed') where
  gbar : (c.ofIsPullback sq).Z ⟶ c.Z
  gbar_eq : gbar = pullback.fst c.g gy
  properSquare : ChosenCartesianSquare gbar (c.ofIsPullback sq).g c.g gy
  openSquare : OpenImmersionSquare gx (c.ofIsPullback sq).i c.i gbar
  complete : ∀ (r : ℕ) (v : Fin r → PbcIntegralRing l E)
    (hv : Ideal.span (Set.range v) = (pbcIntegralDatum l E).ideal)
    (K : sfIntegralConstructibleCategory l E X),
    cbcCompleteProperty (pbcIntegralDatum l E) X r v hv
      ((integralDetailedTransport X l E).obj K.obj)
  equation : ∀ (r : ℕ) (v : Fin r → PbcIntegralRing l E)
      (hv : Ideal.span (Set.range v) = (pbcIntegralDatum l E).ideal)
      (K : sfIntegralConstructibleCategory l E X),
    (integralDetailedTransport Y' l E).map (beta.hom.app K).hom =
      (t.pull gy).hom.app ((SpIntegralAdjunction.support l E c s.support_closed).obj K) ≫
        ((pbcIntegralDatum l E).completedPull gy).map ((t.support c).hom.app K.obj) ≫
        completedCompactSupportExchange (pbcIntegralDatum l E) c (c.ofIsPullback sq)
          gbar properSquare openSquare r v hv
          ⟨(integralDetailedTransport X l E).obj K.obj, complete r v hv K⟩ ≫
        (cbcSupport (pbcIntegralDatum l E) (c.ofIsPullback sq)).map
          ((t.pull gx).inv.app K) ≫
        (t.support (c.ofIsPullback sq)).inv.app
          ((constructibleIntegralPullback l E gx).obj K).obj


/-- Restrict the actual completed pullback/twist/shift to constructibles, retaining
its existing ambient functor.
Source: integral geometric realization, H
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def H {U T : Scheme.{u}} (h : U ⟶ T) (d : ℕ)
    (hc : ∀ K : sfIntegralConstructibleCategory l E T,
      sfIntegralConstructible l E U
        ((SpTwistedPullback.source l E h (d : ℤ) (2 * (d : ℤ))).obj K)) :
    sfIntegralConstructibleCategory l E T ⥤ sfIntegralConstructibleCategory l E U :=
  ObjectProperty.lift _ (SpTwistedPullback.source l E h (d : ℤ) (2 * (d : ℤ))) hc

set_option maxHeartbeats 800000 in
-- The whole-system Tate equation unfolds several composed derived pullback functors.
/-- All factors in the integral Tate comparison are fixed on entire reduction
systems. Its normalization is an equation in the derived category of strict
varying-coefficient systems, not merely an equation after finite evaluation.
Source: integral geometric realization, H and b, proof Steps 6--7
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
structure TateComparison [IsIso gx] (d : ℕ) where
  closed : ∀ K : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E X
      ((SpTwistedPullback.source l E f (d : ℤ) (2 * (d : ℤ))).obj K)
  closed' : ∀ K : sfIntegralConstructibleCategory l E Y',
    sfIntegralConstructible l E X'
      ((SpTwistedPullback.source l E f' (d : ℤ) (2 * (d : ℤ))).obj K)
  model : SourceModel l E b o q f s.rX s.rY d
  model' : SourceModel l E b o q f' s.rX' s.rY' d
  realization : H l E f d closed ⋙ (sfIntegralConstructible l E X).ι ≅
    SpExceptionalBaseChange.red l E b q s.rY ⋙ towerSource l E b o q f s.rX d ⋙
      (SpTowerCalculus.realization l E b X (q.abelian X)).inverse ⋙
        SpExceptionalBaseChange.lim l E b q s.rX
  realization_unit : ∀ K : sfIntegralConstructibleCategory l E Y,
    realization.hom.app K =
      s.rX.normalization.adjunction.unit.app ((H l E f d closed).obj K).obj ≫
        (SpExceptionalBaseChange.lim l E b q s.rX).map
          ((SpTowerCalculus.realization l E b X (q.abelian X)).unitIso.hom.app _ ≫
            (SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map
              (model.comparison.hom.app K))
  towerComparison : towerSource l E b o q f s.rX d ⋙
      SpTowerShriek.pull l E b (o.geometry gx) ≅
    SpTowerMate.V l E b o q a ⋙ towerSource l E b o q f' s.rX' d
  tower_normalization : ∀ K : SpTowerCalculus.C l E b q Y,
    towerComparison.app K = towerTateWord l E b o q a s d K
  comparison : H l E f d closed ⋙ constructibleIntegralPullback l E gx ≅
    constructibleIntegralPullback l E gy ⋙ H l E f' d closed'
  reduction : ∀ K : sfIntegralConstructibleCategory l E Y,
    (SpTowerCalculus.realization l E b X' (q.abelian X')).functor.map
        ((SpExceptionalBaseChange.red l E b q s.rX').map
          (comparison.hom.app K)).hom =
      (SpTowerCalculus.realization l E b X' (q.abelian X')).functor.map
          (s.pullComparison.hom.app ((H l E f d closed).obj K)).hom ≫
        (SpTowerCalculus.realization l E b X' (q.abelian X')).counitIso.hom.app _ ≫
        (SpTowerShriek.pull l E b (o.geometry gx)).map (model.comparison.hom.app K) ≫
        towerComparison.hom.app ((SpExceptionalBaseChange.red l E b q s.rY).obj K) ≫
        (towerSource l E b o q f' s.rX' d).map (s.pullComparison'.inv.app K) ≫
        model'.comparison.inv.app ((constructibleIntegralPullback l E gy).obj K)

/-- The smooth integral adjunction package, with compactification instances
transported along its defining equality. All its reductions, units, counits and
purity components are the ones already specified in the dependency.
Source: integral geometric realization, Step 5 and Purity paragraph
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def SmoothRealization {U T : Scheme.{u}} {h : U ⟶ T} [QuasiCompact h]
    (c₀ : Compactification h) (d : ℕ)
    (rU : SpExceptionalBaseChange.IntegralCoordinates l E b q U)
    (rT : SpExceptionalBaseChange.IntegralCoordinates l E b q T)
    (hF : ∀ M : SpTowerCalculus.C l E b q U,
      spConstructibleTorTowers l E T (q.abelian T)
        ((SpTowerCalculus.F l E b o q c₀).obj M.obj))
    (G : SpTowerCalculus.C l E b q T ⥤ SpTowerCalculus.C l E b q U)
    (adj : SpTowerGluing.support l E b o q c₀ hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q c₀ hF G adj) : Type _ :=
  letI : QuasiCompact (c₀.i ≫ c₀.g) := c₀.comm ▸ inferInstance
  letI : HasCompactification (c₀.i ≫ c₀.g) :=
    (SpTowerGamma.factorization c₀.i c₀.g).hasCompactification
  Σ w : SpChartAdmissibility.Twists l E U,
    Σ lv₀ : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization c₀.i c₀.g) hF G adj,
      { _r : SpIntegralAdjunction.Realization l E b o q c₀.i c₀.g d w
          rU.reduction rU.normalization rT.reduction rT.normalization hF G adj lv₀ //
        HEq lv₀ lv }

/-- Equality with the actual integral purity word in the adjunction dependency,
followed by the unique counit-preserving right-adjoint comparison. This is a
predicate on the requested map, not another definition of integral purity.
Source: integral geometric realization, gamma and the independent adjoint
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def SmoothGammaRealization (d : ℕ)
    (m : SmoothRealization l E b o q c d s.rX s.rY
      a.support_closed a.right a.adjunction a.levels)
    (hc : ∀ K : sfIntegralConstructibleCategory l E Y,
      sfIntegralConstructible l E X
        ((SpTwistedPullback.source l E f (d : ℤ) (2 * (d : ℤ))).obj K))
    (g : H l E f d hc ⟶ s.right) : Prop :=
  letI : QuasiCompact (c.i ≫ c.g) := c.comm ▸ s.quasiCompact
  letI : HasCompactification (c.i ≫ c.g) :=
    (SpTowerGamma.factorization c.i c.g).hasCompactification
  letI : IsNoetherian X := m.2.2.val.noetherianX
  letI : IsNoetherian Y := m.2.2.val.noetherianY
  ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (g.app K).hom
      (s.rX.normalization.adjunction.unit.app
          ((SpTwistedPullback.source l E (c.i ≫ c.g)
            (d : ℤ) (2 * (d : ℤ))).obj K) ≫
        (SpExceptionalBaseChange.lim l E b q s.rX).map
          ((SpTowerCalculus.realization l E b X (q.abelian X)).unitIso.hom.app _ ≫
            (SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map
              (m.2.2.val.sourceComparison.hom.app K ≫
                SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization c.i c.g) m.1 d
                  m.2.2.val.purity.tensorX m.2.2.val.purity.tensorY
                  a.support_closed a.right a.adjunction
                  m.2.2.val.purity.unit_mem m.2.2.val.purity.orientation
                  ((SpExceptionalBaseChange.red l E b q s.rY).obj K)
                  (m.2.2.val.purity.tensor_mem _) (m.2.2.val.purity.projection_iso _)) ≫
            (SpTowerCalculus.realization l E b X (q.abelian X)).unitIso.inv.app _) ≫
        ((m.2.2.val.adjunction.rightAdjointUniq s.adjunction).hom.app K).hom)

/-- Equality with the actual integral purity word in the adjunction dependency,
followed by the unique counit-preserving right-adjoint comparison. This is a
predicate on the primed requested map, not another definition of integral purity.
Source: integral geometric realization, gamma and the independent adjoint
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def SmoothGammaPrimeRealization (d : ℕ)
    (m : SmoothRealization l E b o q (c.ofIsPullback sq) d s.rX' s.rY'
      a.support_closed' a.right' a.adjunction' a.levels')
    (hc : ∀ K : sfIntegralConstructibleCategory l E Y',
      sfIntegralConstructible l E X'
        ((SpTwistedPullback.source l E f' (d : ℤ) (2 * (d : ℤ))).obj K))
    (g : H l E f' d hc ⟶ s.right') : Prop :=
  letI : QuasiCompact ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g) :=
    (c.ofIsPullback sq).comm ▸ s.quasiCompact'
  letI : HasCompactification ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g) :=
    (SpTowerGamma.factorization (c.ofIsPullback sq).i (c.ofIsPullback sq).g).hasCompactification
  letI : IsNoetherian X' := m.2.2.val.noetherianX
  letI : IsNoetherian Y' := m.2.2.val.noetherianY
  ∀ K : sfIntegralConstructibleCategory l E Y',
    HEq (g.app K).hom
      (s.rX'.normalization.adjunction.unit.app
          ((SpTwistedPullback.source l E ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g)
            (d : ℤ) (2 * (d : ℤ))).obj K) ≫
        (SpExceptionalBaseChange.lim l E b q s.rX').map
          ((SpTowerCalculus.realization l E b X' (q.abelian X')).unitIso.hom.app _ ≫
            (SpTowerCalculus.realization l E b X' (q.abelian X')).inverse.map
              (m.2.2.val.sourceComparison.hom.app K ≫
                SpTowerGamma.gamma l E b o q
                  (SpTowerGamma.factorization (c.ofIsPullback sq).i (c.ofIsPullback sq).g) m.1 d
                  m.2.2.val.purity.tensorX m.2.2.val.purity.tensorY
                  a.support_closed' a.right' a.adjunction'
                  m.2.2.val.purity.unit_mem m.2.2.val.purity.orientation
                  ((SpExceptionalBaseChange.red l E b q s.rY').obj K)
                  (m.2.2.val.purity.tensor_mem _) (m.2.2.val.purity.projection_iso _)) ≫
            (SpTowerCalculus.realization l E b X' (q.abelian X')).unitIso.inv.app _) ≫
        ((m.2.2.val.adjunction.rightAdjointUniq s.adjunction').hom.app K).hom)

variable [QuasiCompact (c.i ≫ c.g)] [HasCompactification (c.i ≫ c.g)]
  [QuasiCompact ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g)]
  [HasCompactification ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g)]

/-- Realization of every arrow of the diagram. The smooth package supplies the
specified realized gamma, eta and epsilon. The actual completed exchange is fixed
separately, and the exceptional comparison is both its adjoint transpose and the
reconstruction of the entire tower mate. No independent finite-level lift occurs.
Source: integral geometric realization, all conclusions
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
structure Diagram [IsIso gx] [IsIso gy] (d : ℕ)
    (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x)) where
  coefficients : CoefficientTransport l E
  pullX : PullLimit l E b o q gx s.rX' s.rX s.pullModel
  pullY : PullLimit l E b o q gy s.rY' s.rY s.pullModel'
  reindexX : PurCompletedReindexingAt (pbcIntegralDatum l E) gx
  reindexY : PurCompletedReindexingAt (pbcIntegralDatum l E) gy
  injectiveX : PreservesKInjectives l E gx
  injectiveY : PreservesKInjectives l E gy
  varyingInjectiveX : ∀ I : CochainComplex (SpTowerShriek.S l E X) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      (((o.geometry gx).pull.mapHomologicalComplex (.up ℤ)).obj I)
  varyingInjectiveY : ∀ I : CochainComplex (SpTowerShriek.S l E Y) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      (((o.geometry gy).pull.mapHomologicalComplex (.up ℤ)).obj I)
  tate : TateComparison l E b o q a s d
  smooth : SmoothRealization l E b o q c d s.rX s.rY
    a.support_closed a.right a.adjunction a.levels
  smooth' : SmoothRealization l E b o q (c.ofIsPullback sq) d s.rX' s.rY'
    a.support_closed' a.right' a.adjunction' a.levels'
  reconstruction : HEq smooth.2.2.val.toReconstruction s.supportModel
  reconstruction' : HEq smooth'.2.2.val.toReconstruction s.supportModel'
  gamma : H l E f d tate.closed ≅ s.right
  gamma_realization : SmoothGammaRealization l E b o q a s d smooth tate.closed gamma.hom
  gamma' : H l E f' d tate.closed' ≅ s.right'
  gamma'_realization :
    SmoothGammaPrimeRealization l E b o q a s d smooth' tate.closed' gamma'.hom
  image : SpIntegralAdjunction.support l E c s.support_closed ⋙
      (sfIntegralConstructible l E Y).ι ≅
    SpExceptionalBaseChange.red l E b q s.rX ⋙
      SpTowerGluing.support l E b o q c a.support_closed ⋙
        SpTowerCalculus.inclusion l E b q Y ⋙ SpExceptionalBaseChange.lim l E b q s.rY
  image_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    image.app K = s.supportModel.imageComparison K
  independent : ∀ (G : sfIntegralConstructibleCategory l E Y ⥤
      sfIntegralConstructibleCategory l E X)
      (adj : SpIntegralAdjunction.support l E c s.support_closed ⊣ G),
    Functor.whiskerRight (s.adjunction.rightAdjointUniq adj).hom
        (SpIntegralAdjunction.support l E c s.support_closed) ≫ adj.counit =
      s.adjunction.counit
  beta : SpIntegralAdjunction.support l E c s.support_closed ⋙
      constructibleIntegralPullback l E gy ≅
    constructibleIntegralPullback l E gx ⋙
      SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed'
  exchange : CompletedExchange l E b o q a s coefficients beta
  exchange_reduction : ∀ K : sfIntegralConstructibleCategory l E X,
    (SpExceptionalBaseChange.red l E b q s.rY').map (beta.hom.app K) =
      SpExceptionalBaseChange.exchangeReduction l E b o q a s x K
  exceptional : s.right ⋙ constructibleIntegralPullback l E gx ≅
    constructibleIntegralPullback l E gy ⋙ s.right'
  exceptional_reconstruction : ∀ K : sfIntegralConstructibleCategory l E Y,
    exceptional.hom.app K = SpExceptionalBaseChange.reconstructed l E b o q a s x hb K
  exceptional_limit : ∀ K : sfIntegralConstructibleCategory l E Y,
    SpExceptionalBaseChange.IsLimitRealization l E b o q a s x hb K
  exceptional_transpose : ∀ K : sfIntegralConstructibleCategory l E Y,
    exceptional.hom.app K = SpExceptionalBaseChange.integralTranspose l E b o q a s beta K
  unit : ∀ M : sfIntegralConstructibleCategory l E X,
    HEq ((SpExceptionalBaseChange.red l E b q s.rX).map (s.adjunction.unit.app M))
      (a.adjunction.unit.app ((SpExceptionalBaseChange.red l E b q s.rX).obj M) ≫
        a.right.map (s.supportComparison.inv.app M) ≫ s.exceptionalComparison.inv.app _)
  unit' : ∀ M : sfIntegralConstructibleCategory l E X',
    HEq ((SpExceptionalBaseChange.red l E b q s.rX').map (s.adjunction'.unit.app M))
      (a.adjunction'.unit.app ((SpExceptionalBaseChange.red l E b q s.rX').obj M) ≫
        a.right'.map (s.supportComparison'.inv.app M) ≫ s.exceptionalComparison'.inv.app _)

/-- Reconstruction data for the two compactifications, excluding all reindexing,
Tate, support-exchange and exceptional-mate assertions.
Source: integral-adjunction-bijection, Bijections and Purity
(blueprint: def-pur-integral-geometric-comparison-data). -/
structure SmoothPart (d : ℕ) where
  smooth : SmoothRealization l E b o q c d s.rX s.rY
    a.support_closed a.right a.adjunction a.levels
  smooth' : SmoothRealization l E b o q (c.ofIsPullback sq) d s.rX' s.rY'
    a.support_closed' a.right' a.adjunction' a.levels'
  reconstruction : HEq smooth.2.2.val.toReconstruction s.supportModel
  reconstruction' : HEq smooth'.2.2.val.toReconstruction s.supportModel'
  unit : ∀ M : sfIntegralConstructibleCategory l E X,
    HEq ((SpExceptionalBaseChange.red l E b q s.rX).map (s.adjunction.unit.app M))
      (a.adjunction.unit.app ((SpExceptionalBaseChange.red l E b q s.rX).obj M) ≫
        a.right.map (s.supportComparison.inv.app M) ≫ s.exceptionalComparison.inv.app _)
  unit' : ∀ M : sfIntegralConstructibleCategory l E X',
    HEq ((SpExceptionalBaseChange.red l E b q s.rX').map (s.adjunction'.unit.app M))
      (a.adjunction'.unit.app ((SpExceptionalBaseChange.red l E b q s.rX').obj M) ≫
        a.right'.map (s.supportComparison'.inv.app M) ≫ s.exceptionalComparison'.inv.app _)

/-- Inverse-image and limit data only; no purity or compact-support comparison is asserted.
Source: integral geometric realization, Steps 2--4
(blueprint: def-pur-integral-geometric-comparison-data). -/
structure ReindexingPart [IsIso gx] [IsIso gy] where
  pullX : PullLimit l E b o q gx s.rX' s.rX s.pullModel
  pullY : PullLimit l E b o q gy s.rY' s.rY s.pullModel'
  reindexX : PurCompletedReindexingAt (pbcIntegralDatum l E) gx
  reindexY : PurCompletedReindexingAt (pbcIntegralDatum l E) gy
  varyingInjectiveX : ∀ I : CochainComplex (SpTowerShriek.S l E X) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      (((o.geometry gx).pull.mapHomologicalComplex (.up ℤ)).obj I)
  varyingInjectiveY : ∀ I : CochainComplex (SpTowerShriek.S l E Y) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      (((o.geometry gy).pull.mapHomologicalComplex (.up ℤ)).obj I)

/-- Pullback/twist/shift comparison and the two realized smooth purity maps only.
Source: integral geometric realization, Steps 6--7
(blueprint: def-pur-integral-geometric-comparison-data). -/
structure PurityPart [IsIso gx] (d : ℕ) (m : SmoothPart l E b o q a s d) where
  tate : TateComparison l E b o q a s d
  gamma : H l E f d tate.closed ≅ s.right
  gamma_realization : SmoothGammaRealization l E b o q a s d m.smooth tate.closed gamma.hom
  gamma' : H l E f' d tate.closed' ≅ s.right'
  gamma'_realization :
    SmoothGammaPrimeRealization l E b o q a s d m.smooth' tate.closed' gamma'.hom


end Square

/-- Specialize the diagram to the actual geometric-Frobenius square. Its
isomorphism and prime-invertibility instances are consequences of the standing
conventions, not additional geometric hypotheses. The source copies are retagged
when applying k-linear tower statements; the underlying scheme square is unchanged.
Source: integral geometric realization, hypotheses and proof Step 1
(blueprint: lem-pur-integral-geometric-comparison-realization). -/
def Result (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (d : ℕ)
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] : Prop :=
  let l₀ := P.coefficients.l
  let E₀ := P.extension
  let geom := P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d
  letI : IsIso (P.frobeniusGaloisMap X₀) := geom.1
  letI : IsIso (P.frobeniusGaloisMap Y₀) := geom.2.1
  letI : ∀ x : (P.frobeniusFiber X₀).left,
      Invertible (l₀ : (P.frobeniusFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible P.field l₀ P.coefficients.different X₀
  letI : ∀ y : (P.frobeniusFiber Y₀).left,
      Invertible (l₀ : (P.frobeniusFiber Y₀).left.residueField y) :=
    sfWeilPrimeInvertible P.field l₀ P.coefficients.different Y₀
  ∃ (b₀ : SpTowerShriek.Base l₀ E₀) (o₀ : SpTowerShriek.Operations l₀ E₀ b₀)
    (q₀ : SpTowerCalculus.Coordinates l₀ E₀ b₀)
    (x₀ : SpTowerShriek.OpenExchange l₀ E₀ b₀ o₀)
    (c₀ : Compactification (P.frobeniusMap f₀))
    (a₀ : SpTowerMate.Data l₀ E₀ b₀ o₀ q₀ geom.2.2.1 c₀)
    (hb₀ : IsIso (SpTowerMate.beta l₀ E₀ b₀ o₀ q₀ a₀ x₀))
    (s₀ : SpExceptionalBaseChange.IntegralData l₀ E₀ b₀ o₀ q₀ a₀),
    letI : QuasiCompact (P.frobeniusMap f₀) := s₀.quasiCompact
    letI : QuasiCompact (c₀.i ≫ c₀.g) := c₀.comm ▸ s₀.quasiCompact
    letI : HasCompactification (c₀.i ≫ c₀.g) :=
      (SpTowerGamma.factorization c₀.i c₀.g).hasCompactification
    let c₁ := c₀.ofIsPullback geom.2.2.1
    letI : QuasiCompact (c₁.i ≫ c₁.g) := c₁.comm ▸ s₀.quasiCompact'
    letI : HasCompactification (c₁.i ≫ c₁.g) :=
      (SpTowerGamma.factorization c₁.i c₁.g).hasCompactification
    Nonempty (Diagram l₀ E₀ b₀ o₀ q₀ a₀ s₀ d x₀ hb₀)


end AlgebraicGeometry.ProEtale.IntegralGeometricComparison
