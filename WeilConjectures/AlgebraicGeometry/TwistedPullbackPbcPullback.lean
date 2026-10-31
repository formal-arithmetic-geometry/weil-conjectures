/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackPbcCoordinates
public import WeilConjectures.AlgebraicGeometry.FdPullbackComparison
public import WeilConjectures.AlgebraicGeometry.CompletedCoefficientPresentationTransport
public import WeilConjectures.AlgebraicGeometry.FdCoefficientComparison

/-! # Whole-tower PBC pullback coordinates and the scalar/pullback square

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
common strict quotient tower and identification of p
(blueprint: def-pur-twisted-pullback-pbc-pullback-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open Opposite CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual strict pullback tower endomorphism, before realization.
Source: purity transport, common strict quotient tower, proof step 7
(blueprint: def-pur-twisted-pullback-pbc-pullback-coordinates). -/
def coordinatePullbackEndomorphism {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l (E) T) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralOperationsPullbackTowerFunctor l
      (E) h).obj P).obj (op n))
    (integralOperationsTowerStep
      ((integralOperationsPullbackTowerFunctor l (E) h).obj P))

/-- The canonical quotient projection from the whole strict pullback cone, in one degree.
Source: purity transport, common strict quotient tower, proof step 7
(blueprint: def-pur-twisted-pullback-pbc-pullback-coordinates). -/
def coordinatePullbackProjection {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l (E) T) ℤ)
    (i : ℤ) (n : ℕ) :=
  (CochainComplex.mappingCocone.fst (coordinatePullbackEndomorphism l E h P)).f i ≫
    (Pi.π (fun n ↦ ((integralOperationsPullbackTowerFunctor l
      (E) h).obj P).obj (op n)) n).f i

/-- A whole-tower pullback comparison fixed by every quotient-unit component and zero
shifted component. In particular it cannot be inferred from equality of isolated reductions.
Source: purity transport, common strict quotient tower, proof steps 7--8
(blueprint: def-pur-twisted-pullback-pbc-pullback-coordinates). -/
structure CoordinatePullbackChain {U T : Scheme.{u}} (h : U ⟶ T) where
  map :
    (fdCoefficientTransport l (E) T).mapHomologicalComplex (.up ℤ) ⋙
        (pbcActualModulePull h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) ⟶
      integralOperationsPullbackComplexFunctor l (E) h ⋙
        (fdCoefficientTransport l (E) U).mapHomologicalComplex (.up ℤ)
  quotients : ∀ (P : CochainComplex
      (integralTowerModules l (E) T) ℤ)
    (i : ℤ) (n : ℕ) (V : T.ProEt) (x : (P.X i).val.obj (op V))
    (x' : ((fdCoefficientTransport l (E) T).obj
      (P.X i)).val.obj (op V)), HEq x' x →
    HEq (((map.app P).f i ≫
        (fdCoefficientTransport l (E) U).map
          (coordinatePullbackProjection l E h P i n)).val.app
      (op ((proEtaleBaseChange h).obj V))
      (pbcActualModuleUnitSection h (pbcIntegralDatum l E)
        ((fdCoefficientTransport l (E) T).obj (P.X i)) V x'))
      (integralOperationsPullbackGenerator l (E) h n
        (((unrestrictedIntegralFiniteComplex l (E) T n).obj P).X i)
        V (coefficientIntegralScalarUnitSection l (E) T n
          (P.X i) (op V) x))
  shifted : ∀ (P : CochainComplex
      (integralTowerModules l (E) T) ℤ) (i : ℤ),
    (map.app P).f i ≫ (fdCoefficientTransport l (E) U).map
      ((CochainComplex.mappingCocone.snd (coordinatePullbackEndomorphism l E h P)).v
        i (i - 1) (by omega)) = 0

/-- Pullback identification for an arbitrary morphism. The unit equation fixes it on
all good representatives by the common strict quotient tower, including every
transition and the zero shifted coordinate. Its rational map is the localization.
Source: purity transport, comparison pi of the common integral presentations
(blueprint: def-pur-twisted-pullback-pbc-pullback-coordinates). -/
structure PullCoordinates {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (JX : Presentation l E X) (JY : Presentation l E Y) (h : X ⟶ Y) where
  chain : CoordinatePullbackChain l E h
  preserves : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualCompletedPull h (pbcIntegralDatum l E)).obj K.obj)
  integral : JY.integral.functor ⋙
      pbcConditionalIntegral (pbcIntegralDatum l E)
        (pbcActualCompletedPull h (pbcIntegralDatum l E)) preserves ≅
    constructibleIntegralPullback l E h ⋙ JX.integral.functor
  ambient : (sfIntegralConstructible l E Y).ι ⋙ integralDetailedTransport Y l E ⋙
      pbcActualCompletedPull h (pbcIntegralDatum l E) ≅
    constructibleIntegralPullback l E h ⋙ (sfIntegralConstructible l E X).ι ⋙
      integralDetailedTransport X l E
  lift : ∀ K, HEq (integral.hom.app K).hom (ambient.hom.app K)
  normalization : ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj)),
    HEq ((pbcActualCompletedPullUnit h (pbcIntegralDatum l E)).app
        ((integralDetailedTransport Y l E).obj (DerivedCategory.Q.obj P.obj)) ≫
      ambient.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport X l E).map
        ((integralDerivedPullbackComparison l E h).hom.app P) ≫
      (fdCoefficientTransportFactors l E X).hom.app
        ((integralOperationsPullbackComplexFunctor l E h).obj P.obj))
      ((pbcActualDerivedPull h (pbcIntegralDatum l E)).map
        ((fdCoefficientTransportFactors l E Y).hom.app P.obj) ≫
      pbcActualPullComplexCounit h (pbcIntegralDatum l E)
        (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map (chain.map.app P.obj))
  rational : JY.rational.functor ⋙
      pbcConditionalRational (pbcIntegralDatum l E)
        (pbcActualCompletedPull h (pbcIntegralDatum l E)) preserves (pbcUniformizer l E) ≅
    rationalDerivedPullback l E h ⋙ JX.rational.functor
  rationalization : ∀ K,
    HEq (rational.hom.app ((sfRationalConstructibleLocalization l E Y).obj K))
      ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (integral.hom.app K))

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- Conjugation identifies the framework p with the specified PBC completed-pullback
comparison, in its correct inverse direction. Every map is already fixed by the
whole-tower unit equation or the completion-chi normalization.
Source: purity transport, scalar/pullback identification
(blueprint: def-pur-twisted-pullback-pbc-pullback-coordinates). -/
def PullScalarCompatible {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {JXE : Presentation l E X} {JXL : Presentation l L X}
    {JYE : Presentation l E Y} {JYL : Presentation l L Y} (h : X ⟶ Y)
    (PE : PullCoordinates l E JXE JYE h) (PL : PullCoordinates l L JXL JYL h)
    (SX : ScalarCoordinates l E L i X JXE JXL)
    (SY : ScalarCoordinates l E L i Y JYE JYL) : Prop :=
  ∀ K : sfIntegralConstructibleCategory l E Y,
    (pbcEmbeddingAmbientTensor l E L i X).map (PE.ambient.hom.app K) ≫
      SX.ambient.hom.app ((constructibleIntegralPullback l E h).obj K) ≫
      (integralDetailedTransport X l L).map
        (integralPullbackScalarComparison l E L i h K).hom.hom =
    (pbcScalarCompletedPullIso l E L i h).inv.app
        ((integralDetailedTransport Y l E).obj K.obj) ≫
      (pbcActualCompletedPull h (pbcIntegralDatum l L)).map (SY.ambient.hom.app K) ≫
      PL.ambient.hom.app ((integralScalar l E L i Y).obj K)

end WeilConjectures.TwistedPullbackScalars
