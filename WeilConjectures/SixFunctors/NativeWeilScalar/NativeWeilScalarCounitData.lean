/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeWeilScalar.NativeWeilScalarCounitCategories
public import WeilConjectures.SixFunctors.ExceptionalFieldDescent.ExceptionalFieldDescent

/-! # Normalized scalar and Frobenius counit data

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance, native expansion Steps 1--17
(blueprint: def-sf-native-weil-scalar-counit-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.privateModule false
attribute [local irreducible] HasDerivedCategory.standard
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeWeilScalar
open AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (R : Family l D)
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
  [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (c₀ : Compactification f₀.left)

/-- Inherited geometric-fiber property used by the recorded common-stage operations.
Source: native expansion, opening paragraph and Step 14
(blueprint: def-sf-native-weil-scalar-counit-data). -/
instance rawTargetFinite : LocallyOfFiniteType
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀).left ↘
      Spec (.of D.k)) := (FrobeniusExchange.fiber_finiteType D Y₀).1
/-- Inherited geometric-fiber property used by the recorded common-stage operations.
Source: native expansion, opening paragraph and Step 14
(blueprint: def-sf-native-weil-scalar-counit-data). -/
instance rawTargetQc : QuasiCompact
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀).left ↘
      Spec (.of D.k)) := (FrobeniusExchange.fiber_finiteType D Y₀).2

/-- Inherited geometric-fiber property used by the recorded common-stage operations.
Source: native expansion, opening paragraph and Step 14
(blueprint: def-sf-native-weil-scalar-counit-data). -/
instance fiberRelativeSeparated : IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
  (FrobeniusExchange.fiberMap_properties D f₀).1
/-- Inherited geometric-fiber property used by the recorded common-stage operations.
Source: native expansion, opening paragraph and Step 14
(blueprint: def-sf-native-weil-scalar-counit-data). -/
instance fiberRelativeFinite : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
  (FrobeniusExchange.fiberMap_properties D f₀).2.1
/-- Inherited geometric-fiber property used by the recorded common-stage operations.
Source: native expansion, opening paragraph and Step 14
(blueprint: def-sf-native-weil-scalar-counit-data). -/
instance fiberRelativeQc : QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
  (FrobeniusExchange.fiberMap_properties D f₀).2.2

/-- The normalized ordinary comparison, its constructible adjunction, and its actual
Frobenius mate. All the following fields are conclusions, not hypotheses.
Source: native expansion, Steps 13--17
(blueprint: def-sf-native-weil-scalar-counit-data). -/
structure CounitData (Ff : (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
  ((fiberSpace D X₀).base.left)) ⥤ (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
  ((fiberSpace D Y₀).base.left))) (Gf : (generalAlgebraicallyClosedConstructibleCategory l
  (PadicAlgCl l) ((fiberSpace D Y₀).base.left)) ⥤ (generalAlgebraicallyClosedConstructibleCategory l
  (PadicAlgCl l) ((fiberSpace D X₀).base.left))) (ad : Ff ⊣ Gf)
    (G : LocallyFiniteAdicCompactSupport.NativeGeometry.{u} l) where
  source : EquivalenceData l D R (fiberSpace D X₀)
  target : EquivalenceData l D R (fiberSpace D Y₀)
  alpha : Ff ⋙ ordinary l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D Y₀)).realization ≅
    ordinary l ((fiberSpace D X₀).base.left) (R.data (fiberSpace D X₀)).realization ⋙
      compact l (FrobeniusExchange.geometricCompactification D f₀ c₀) (R.data (fiberSpace D
        X₀)).realization (R.data (fiberSpace D Y₀)).realization G
  preserves : ∀ K : (Constructible l ((fiberSpace D X₀).base.left) (R.data (fiberSpace D
    X₀)).realization), boundedConstructible l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D
    Y₀)).realization
    ((compact l (FrobeniusExchange.geometricCompactification D f₀ c₀) (R.data (fiberSpace D
      X₀)).realization (R.data (fiberSpace D Y₀)).realization G).obj K.obj)
  leftIdentification :
    source.equivalence.inverse ⋙ Ff ⋙ target.equivalence.functor ≅
      restrictCompact l (R.data (fiberSpace D X₀)).realization (R.data (fiberSpace D
        Y₀)).realization
        (compact l (FrobeniusExchange.geometricCompactification D f₀ c₀) (R.data (fiberSpace D
          X₀)).realization (R.data (fiberSpace D Y₀)).realization G) preserves
  identification_normalized : ∀ M,
    (boundedConstructible l (D.geometricFiber Y₀).left
      (R.data (fiberSpace D Y₀)).realization).ι.map (leftIdentification.hom.app M) =
      (realizationBridge l D R (fiberSpace D Y₀) target).hom.app
          (Ff.obj (source.equivalence.inverse.obj M)) ≫
        alpha.hom.app (source.equivalence.inverse.obj M) ≫
        (compact l (FrobeniusExchange.geometricCompactification D f₀ c₀)
          (R.data (fiberSpace D X₀)).realization
          (R.data (fiberSpace D Y₀)).realization G).map
            ((realizationBridge l D R (fiberSpace D X₀) source).inv.app
                (source.equivalence.inverse.obj M) ≫
              (boundedConstructible l (D.geometricFiber X₀).left
                (R.data (fiberSpace D X₀)).realization).ι.map
                  (source.equivalence.counitIso.hom.app M))
  pullX : ∀ K : (Constructible l ((fiberSpace D X₀).base.left) (R.data (fiberSpace D
    X₀)).realization), boundedConstructible l ((fiberSpace D X₀).base.left) (R.data (fiberSpace D
    X₀)).realization
    ((pull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀)).mapDerivedCategory.obj K.obj)
  pullY : ∀ K : (Constructible l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D
    Y₀)).realization), boundedConstructible l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D
    Y₀)).realization
    ((pull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀)).mapDerivedCategory.obj K.obj)
  inversePullX : ∀ K : (Constructible l ((fiberSpace D X₀).base.left) (R.data (fiberSpace D
    X₀)).realization), boundedConstructible l ((fiberSpace D X₀).base.left) (R.data (fiberSpace D
    X₀)).realization
    ((pull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀).symm).mapDerivedCategory.obj K.obj)
  inversePullY : ∀ K : (Constructible l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D
    Y₀)).realization), boundedConstructible l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D
    Y₀)).realization
    ((pull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀).symm).mapDerivedCategory.obj K.obj)
  exchange :
    (source.equivalence.inverse ⋙ Ff ⋙ target.equivalence.functor) ⋙
        restrictPull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀) pullY ≅
      restrictPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀) pullX ⋙
        source.equivalence.inverse ⋙ Ff ⋙ target.equivalence.functor
  inverseExchange :
    (source.equivalence.inverse ⋙ Ff ⋙ target.equivalence.functor) ⋙
        restrictPull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀).symm inversePullY ≅
      restrictPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀).symm inversePullX ⋙
        source.equivalence.inverse ⋙ Ff ⋙ target.equivalence.functor
  inverse_normalized : ∀ M,
    (restrictPull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀).symm inversePullY).map
        (exchange.hom.app M) ≫
      inverseExchange.hom.app
        ((restrictPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀) pullX).obj M) ≫
      (source.equivalence.inverse ⋙ Ff ⋙ target.equivalence.functor).map
        ((constructibleCancel l D R (fiberSpace D X₀) (D.geometricFrobenius X₀)
          pullX inversePullX).hom.app M) =
      (constructibleCancel l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀)
        pullY inversePullY).hom.app
          ((source.equivalence.inverse ⋙ Ff ⋙ target.equivalence.functor).obj M)
  mate_isIso : IsIso (mate (transportAdjunction source.equivalence target.equivalence ad)
    (restrictPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀) pullX) (restrictPull l D R
      (fiberSpace D Y₀) (D.geometricFrobenius Y₀) pullY) exchange)
  counit : MateCounit (transportAdjunction source.equivalence target.equivalence ad)
    (restrictPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀) pullX) (restrictPull l D R
      (fiberSpace D Y₀) (D.geometricFrobenius Y₀) pullY) exchange
  invariant : ∀ [HasDerivedCategory.{u + 1} (Pairs l D R (fiberSpace D Y₀) (D.geometricFrobenius
    Y₀))]
    (L : Weil l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀)),
    InvariantCounit (transportAdjunction source.equivalence target.equivalence ad)
      (restrictPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀) pullX) (restrictPull l D R
        (fiberSpace D Y₀) (D.geometricFrobenius Y₀) pullY) exchange
      ((forgetConstructible l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀)).obj L)
      (constructibleTheta l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀) pullY L)

variable [I : ExceptionalFieldDescent.IntegralInput l D hl
  (FrobeniusExchange.geometricCompactification D f₀ c₀)]
  [J : ExceptionalFieldDescent.RationalOutput l D hl (FrobeniusExchange.geometricCompactification D
    f₀ c₀)]
  (S : ExceptionalFieldDescent.CommonStageData l D hl (FrobeniusExchange.geometricCompactification D
    f₀ c₀) (PadicAlgCl l))
  (O : ExceptionalFieldDescent.CommonOutput l D hl (FrobeniusExchange.geometricCompactification D f₀
    c₀) (PadicAlgCl l) S)

/-- Compatibility of the actual ordinary module exchange with the common-stage
exchange and the fixed realization, spelled out before taking mates.
Here common_normalization compares fixed finite compact-support representatives:
CommonStageData.leftStages already pins these to the literal rationalLeft functor,
unlike the freely presented coefficient construction in ScalarNormalization. The
HEq allows the object equalities of commonStageDerivedPullback's specification.
Source: native expansion, Step 12
(blueprint: def-sf-native-weil-scalar-counit-data). -/
structure FrobeniusNormalization (G : LocallyFiniteAdicCompactSupport.NativeGeometry.{u} l)
    (A : CounitData l D R f₀ c₀ S.leftSystem.functor S.rightSystem.functor O.adjunction G)
    where
  common :
    S.leftSystem.functor ⋙ commonPull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀) ≅
      commonPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀) ⋙ S.leftSystem.functor
  common_normalization : ∀ K : (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
    ((fiberSpace D X₀).base.left)),
    HEq (common.hom.app K)
      ((FrobeniusExchange.frobeniusCommonStage D l hl f₀
        (FrobeniusExchange.frobeniusCompactModel D f₀ c₀) (PadicAlgCl l)).app K)
  actual :
    compact l (FrobeniusExchange.geometricCompactification D f₀ c₀) (R.data (fiberSpace D
      X₀)).realization (R.data (fiberSpace D Y₀)).realization G ⋙
        (pull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀)).mapDerivedCategory ≅
      (pull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀)).mapDerivedCategory ⋙
        compact l (FrobeniusExchange.geometricCompactification D f₀ c₀) (R.data (fiberSpace D
          X₀)).realization (R.data (fiberSpace D Y₀)).realization G
  square : ∀ K : (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) ((fiberSpace D
    X₀).base.left)),
    (R.comparison (fiberSpace D Y₀) (fiberSpace D Y₀) (D.geometricFrobenius Y₀)).hom.app
      (S.leftSystem.functor.obj K) ≫
        (pull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀)).mapDerivedCategory.map
          (A.alpha.hom.app K) ≫
        actual.hom.app ((ordinary l ((fiberSpace D X₀).base.left) (R.data (fiberSpace D
          X₀)).realization).obj K) =
      (ordinary l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D Y₀)).realization).map
        (common.hom.app K) ≫
        A.alpha.hom.app ((commonPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀)).obj K) ≫
        (compact l (FrobeniusExchange.geometricCompactification D f₀ c₀) (R.data (fiberSpace D
          X₀)).realization (R.data (fiberSpace D Y₀)).realization G).map
          ((R.comparison (fiberSpace D X₀) (fiberSpace D X₀) (D.geometricFrobenius X₀)).hom.app K)
  restricted : ∀ M : (Constructible l ((fiberSpace D X₀).base.left) (R.data (fiberSpace D
    X₀)).realization),
    ((boundedConstructible l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D
      Y₀)).realization).ι.map
        (A.exchange.hom.app M)) ≫
        ((boundedConstructible l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D
          Y₀)).realization).ι.map
          (A.leftIdentification.hom.app
            ((restrictPull l D R (fiberSpace D X₀) (D.geometricFrobenius X₀) A.pullX).obj M))) =
      (pull l D R (fiberSpace D Y₀) (D.geometricFrobenius Y₀)).mapDerivedCategory.map
          ((boundedConstructible l ((fiberSpace D Y₀).base.left) (R.data (fiberSpace D
            Y₀)).realization).ι.map
            (A.leftIdentification.hom.app M)) ≫ actual.hom.app M.obj

/-- The scalar comparison is fixed before any mate is taken: its integral components
are the actual proper/open coefficient mate, with the strict-tower coordinate change.
The StageAction fixes every field transition, including identity transitions. Its
bridge from the fixed common functor is the inverse rationalLeft comparison on each
finite representative; no equality of the two presentations is required. The integral
formula and this bridge fix the extension to rational and common-stage arrows.
Source: native expansion, Steps 1--11; condensed realization, factor normalization
(blueprint: def-sf-native-weil-scalar-counit-data). -/
structure ScalarNormalization
    (P : ConstructibleExceptionalCoefficients.CoefficientConstruction l
      (ULift.{u} (PadicAlgCl l)) D hl (f := FrobeniusExchange.fiberMap D f₀))
    [G : LocallyFiniteAdicCompactSupport.NativeGeometry.{u} l]
    (A : CounitData l D R f₀ c₀ S.leftSystem.functor S.rightSystem.functor O.adjunction G)
    where
  stage : LocallyFiniteAdicCompactSupport.StageAction l D hl P
    (FrobeniusExchange.geometricCompactification D f₀ c₀)
  bridge : S.leftSystem.functor ≅ stage.system.functor
  bridge_normalized : ∀ (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l)
        ((fiberSpace D X₀).base.left) E),
    ∃ (M N : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
        ((fiberSpace D Y₀).base.left)) (r : M ⟶ N),
      HEq r ((P.ring.rationalLeft (FrobeniusExchange.geometricCompactification D f₀ c₀)
        (LocallyFiniteAdicCompactSupport.finiteField l E)).inv.app K) ∧
      HEq (bridge.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := (fiberSpace D X₀).base.left) E).obj K))
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := (fiberSpace D Y₀).base.left) E).map r)
  change : ∀ E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l),
    PurCompactSupport.Change (PurCompactSupport.completed l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E))
      (LocallyFiniteAdicCompactSupport.nativeCoefficients l)
  change_source : ∀ E, (change E).map (D.geometricFiber X₀).left = (((R.data (fiberSpace D
    X₀)).realization).coefficient E).integralMap l (D.geometricFiber X₀).left
  change_target : ∀ E, (change E).map (D.geometricFiber Y₀).left = (((R.data (fiberSpace D
    Y₀)).realization).coefficient E).integralMap l (D.geometricFiber Y₀).left
  nativeAlpha : stage.system.functor ⋙ ((R.data (fiberSpace D Y₀)).realization).J ≅ ((R.data
    (fiberSpace D X₀)).realization).J ⋙
    LocallyFiniteAdicCompactSupport.actual l (FrobeniusExchange.geometricCompactification D f₀ c₀)
  integral : LocallyFiniteAdicCompactSupport.IntegralNormalization l D hl P
    (FrobeniusExchange.geometricCompactification D f₀ c₀)
    ((R.data (fiberSpace D X₀)).realization) ((R.data (fiberSpace D Y₀)).realization) stage change
      nativeAlpha
  sections : ∀ K,
    HEq (A.alpha.hom.app K)
      ((LocallyFiniteAdicRealization.sections l (D.geometricFiber Y₀).left).mapDerivedCategory.map
          ((((R.data (fiberSpace D Y₀)).realization).J.map (bridge.hom.app K)) ≫
            nativeAlpha.hom.app K) ≫
        (LocallyFiniteAdicCompactSupport.operationTransport l
          (FrobeniusExchange.geometricCompactification D f₀ c₀)).hom.app (((R.data (fiberSpace D
          X₀)).realization).J.obj K))
  shift :
    letI := O.leftShift
    letI : HasShift (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
        ((fiberSpace D X₀).base.left)) ℤ :=
      WeilConjectures.GeneralAlgebraicallyClosedCoefficients.hasShift
    letI : HasShift (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
        ((fiberSpace D Y₀).base.left)) ℤ :=
      WeilConjectures.GeneralAlgebraicallyClosedCoefficients.hasShift
    letI : (ordinary l (fiberSpace D X₀).base.left
      (R.data (fiberSpace D X₀)).realization).CommShift ℤ := (R.data (fiberSpace D X₀)).shift
    letI : (ordinary l (fiberSpace D Y₀).base.left
      (R.data (fiberSpace D Y₀)).realization).CommShift ℤ := (R.data (fiberSpace D Y₀)).shift
    letI : (compact l (FrobeniusExchange.geometricCompactification D f₀ c₀)
      ((R.data (fiberSpace D X₀)).realization)
      ((R.data (fiberSpace D Y₀)).realization) G).CommShift ℤ := by
      unfold compact PurCompactSupport.image
      infer_instance
    A.alpha.hom.CommShift ℤ

end Geometry
end WeilConjectures.NativeWeilScalar
