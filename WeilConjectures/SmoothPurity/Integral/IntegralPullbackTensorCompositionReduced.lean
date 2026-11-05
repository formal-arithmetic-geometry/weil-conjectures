/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealization
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
import WeilConjectures.SmoothPurity.Integral.IntegralCanonicalPullbackTensorReduction
import WeilConjectures.SmoothPurity.Integral.IntegralSystemCompositionIdentification

/-! The reduced system form of integral pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; the strict quotient-system calculation before reflection.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced)

The former finite-evaluation proof used a false joint-faithfulness assertion.
`integralPullbackTensorCompositionReduced_of_systemLaw` compares whole strict-system
representatives before localization: for every compositor whose reduction is the system
compositor after the whole-system pullback comparisons, the equation reduces to the
composition law of the coherent system pullback/tensor comparison, which descends from
the strict cochain law. The compositor `pullbackTensorIntegralComposition`, chosen from
`integralPullbackComposition`, has this normalization by the last clause of that theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

end WeilConjectures
