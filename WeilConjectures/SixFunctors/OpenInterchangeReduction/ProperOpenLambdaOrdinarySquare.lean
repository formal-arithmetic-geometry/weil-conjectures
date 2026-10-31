/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import WeilConjectures.SixFunctors.OpenInterchangeReduction.ProperOpenLambdaFourFactorSquare

/-! # Ordinary proper/open lambda square

This file isolates the ordinary (pre-completion) part of the proper/open
coefficient square.  The ordinary calculation is the open-adjunction and
clopen factorization; completion is handled separately by the transport
statement below.
(blueprint: lem-sf-proper-open-lambda-reduction-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction

namespace WeilConjectures.OpenInterchangeReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

def ordinaryTensorReductionY9 (d : IntegralSystemRealization.RingedModels l E)
    (X : Scheme.{u}) :
    (d.tensor X).ordinary.tensor ⋙ (IntegralSystemRealization.calculus l E X).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction.prod
        (IntegralSystemRealization.calculus l E X).reduction ⋙
          (IntegralSystemRealization.calculus l E X).systemClosed.tensor :=
  Functor.whiskerRight (eqToIso (d.tensorClosed X)).hom
      (IntegralSystemRealization.calculus l E X).reduction ≫
    (IntegralSystemRealization.calculus l E X).reductionTensor.hom

def ordinaryPushReductionY9 (o : IntegralSystemRealization.Operations l E)
    (m : IntegralSystemRealization.RealizationModel l E o) {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    IntegralSystemRealization.ringedPush l E f ⋙
        (IntegralSystemRealization.calculus l E Y).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction ⋙
        IntegralSystemRealization.Operations.push l E o f :=
  (mateEquiv (IntegralSystemRealization.ringedAdj l E f) (o.direct f).adj
    (m.reductionPull f).inv).natTrans

def properOpenOrdinaryR
    {S : Type s} {W : S → Scheme.{u}} {I : Type i} (location : I → S)
    (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → (B : Word W location a) →
      (IntegralSystemRealization.calculus l E (W a)).reduction.obj
        (B.ringedValue l E W location o K) ⟶
      B.systemValue l E W location o (inputReduction l E W location K)
  | _, .input _ => 𝟙 _
  | a, .unit _ => (o.unitReduction (W a)).hom
  | a, .tensor B C =>
      (ordinaryTensorReductionY9 l E o.ringed (W a)).app
          (B.ringedValue l E W location o K, C.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
          (Prod.mkHom (properOpenOrdinaryR location o K B)
            (properOpenOrdinaryR location o K C))
  | _, .pull f _ _ _ B =>
      (o.realization.reductionPull f).hom.app
          (B.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.pull l E f).map
          (properOpenOrdinaryR location o K B)
  | _, .push f _ _ _ _ B =>
      (ordinaryPushReductionY9 l E o.system o.realization f).app
          (B.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.Operations.push l E o.system f).map
          (properOpenOrdinaryR location o K B)
  | _, .open j hj _ B => letI := hj
      inverseOrZero ((o.realization.openReduction l E j).app
          (B.ringedValue l E W location o K)) ≫
        (IntegralSystemRealization.Operations.shriek l E o.system j).map
          (properOpenOrdinaryR location o K B)

end WeilConjectures.OpenInterchangeReduction
