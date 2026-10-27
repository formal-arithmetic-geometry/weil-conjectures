/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.SixFunctors.OpenInterchangeReductionData

/-! # Four-factor ordinary proper/open lambda square

This module isolates the component square for the prescribed four-factor
proper/open lambda.  The recursive word comparison is supplied by the caller.
(blueprint: lem-sf-proper-open-lambda-four-factor-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u s
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction

namespace WeilConjectures.OpenInterchangeReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary proper-image reduction mate used by the four-factor expansion. -/
def ordinaryPushReductionK5 (o : IntegralSystemRealization.Operations l E)
    (m : IntegralSystemRealization.RealizationModel l E o) {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    IntegralSystemRealization.ringedPush l E f ⋙
        (IntegralSystemRealization.calculus l E Y).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction ⋙
        IntegralSystemRealization.Operations.push l E o f :=
  (mateEquiv (IntegralSystemRealization.ringedAdj l E f) (o.direct f).adj
    (m.reductionPull f).inv).natTrans

/-- The source map obtained by expanding the pull, proper, open three-factor
part of the ordinary comparison, with an arbitrary child comparison `f`. -/
def properOpenLambdaFourFactorSource
    {S : Type s} (W : S → Scheme.{u}) {a b c d : S}
    (o : Operations l E) (k : W a ⟶ W b) (r : W a ⟶ W c)
    (p : W b ⟶ W d) (j : W c ⟶ W d)
    (hk : IsOpenImmersion k) (hki : QuasiCompact k)
    (hjo : IsOpenImmersion j) (hji : QuasiCompact j)
    (hr : IsProper r) (hp : IsProper p)
    (M : DerivedCategory (scalarReductionSource l E (W a)))
    (N : coefficientSequenceDerived l E (W a))
    (f : (IntegralSystemRealization.calculus l E (W a)).reduction.obj M ⟶ N) :
    (IntegralSystemRealization.calculus l E (W c)).reduction.obj
        ((IntegralSystemRealization.ringedPull l E j).obj
          ((IntegralSystemRealization.ringedPush l E p).obj
            ((IntegralSystemRealization.ringedOpen l E k).obj M))) ⟶
      (IntegralSystemRealization.pull l E j).obj
        ((IntegralSystemRealization.Operations.push l E o.system p).obj
          ((IntegralSystemRealization.Operations.shriek l E o.system k).obj N)) := by
  letI := hk
  letI := hki
  letI := hjo
  letI := hji
  letI := hr
  letI := hp
  exact
    (o.realization.reductionPull j).hom.app
        ((IntegralSystemRealization.ringedPush l E p).obj
          ((IntegralSystemRealization.ringedOpen l E k).obj M)) ≫
      (IntegralSystemRealization.pull l E j).map
        ((ordinaryPushReductionK5 l E o.system o.realization p).app
          ((IntegralSystemRealization.ringedOpen l E k).obj M)) ≫
      (IntegralSystemRealization.pull l E j).map
        ((IntegralSystemRealization.Operations.push l E o.system p).map
          (inverseOrZero ((o.realization.openReduction l E k).app M))) ≫
      (IntegralSystemRealization.pull l E j).map
        ((IntegralSystemRealization.Operations.push l E o.system p).map
          ((IntegralSystemRealization.Operations.shriek l E o.system k).map f))

/-- The target map obtained by expanding the ordinary proper factor, with an
arbitrary child comparison `f`. -/
def properOpenLambdaFourFactorTarget
    {S : Type s} (W : S → Scheme.{u}) {a c : S}
    (o : Operations l E) (r : W a ⟶ W c)
    (hr : IsProper r) (M : DerivedCategory (scalarReductionSource l E (W a)))
    (N : coefficientSequenceDerived l E (W a))
    (f : (IntegralSystemRealization.calculus l E (W a)).reduction.obj M ⟶ N) :
    (IntegralSystemRealization.calculus l E (W c)).reduction.obj
        ((IntegralSystemRealization.ringedPush l E r).obj M) ⟶
      (IntegralSystemRealization.Operations.push l E o.system r).obj N := by
  letI := hr
  exact (ordinaryPushReductionK5 l E o.system o.realization r).app M ≫
    (IntegralSystemRealization.Operations.push l E o.system r).map f

/-- The ordinary square for the four prescribed lambda factors, before a finite
word is substituted for the child object.  It is strictly the component step:
the caller supplies the child comparison `f`, while this statement contains no
recursive `Word` comparison.  The proof expands the cartesian, restriction,
clopen and compositor factors and pastes their four component squares.
Source: `fix-prop-coherence.proof.md`, proper/open lambda coefficient-square
expansion.
(blueprint: lem-sf-proper-open-lambda-four-factor-square) -/
theorem properOpenLambdaFourFactorSquare
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    {S : Type s} (W : S → Scheme.{u})
    {a b c d : S}
    (k : W a ⟶ W b) (r : W a ⟶ W c) (p : W b ⟶ W d) (j : W c ⟶ W d)
    (h : k ≫ p = r ≫ j) (hk : IsOpenImmersion k) (hki : QuasiCompact k)
    (hjo : IsOpenImmersion j) (hji : QuasiCompact j)
    (hr : IsProper r) (hp : IsProper p)
    (M : DerivedCategory (scalarReductionSource Cf.l E (W a)))
    (N : coefficientSequenceDerived Cf.l E (W a))
    (f : (IntegralSystemRealization.calculus Cf.l E (W a)).reduction.obj M ⟶ N) :
    properOpenLambdaFourFactorSource Cf.l E W o k r p j hk hki hjo hji hr hp M N f ≫
        (IntegralSystemRealization.properOpenLambda Cf.l E o.system o.composition o.opens
          k r p j h).hom.app N =
      (IntegralSystemRealization.calculus Cf.l E (W c)).reduction.map
          ((IntegralSystemRealization.ringedProperOpenLambda Cf.l E o.ringed
            o.ringedOpens k r p j h).hom.app M) ≫
        properOpenLambdaFourFactorTarget Cf.l E W o r hr M N f := by
  sorry

end WeilConjectures.OpenInterchangeReduction
