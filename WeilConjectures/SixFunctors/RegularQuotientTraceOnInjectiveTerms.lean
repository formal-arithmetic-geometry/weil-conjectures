/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
import WeilConjectures.SixFunctors.Regular.RegularQuotientInjectiveKernel
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAdjoint

/-! Termwise-injective computation of the regular quotient trace.

Source: Stacks Tags 06YY, 07A6, 0A70, 0BZE, 0BZH and 08FZ;
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

private local instance (T : Scheme.{u}) : EssentiallySmall.{u+1} T.ProEt :=
  essentiallySmallSelf.{0,u,u+1} _
private local instance (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u,u} T
private local instance (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u,u} T
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

/-- The normalized regular quotient trace is invertible on a complex with injective terms.
Source: Stacks Tags 06YY, 07A6, 0A70, 0BZE, 0BZH and 08FZ; the principal short exact
sequence of complexes and its cone-boundary/coinduction comparison.
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms).

Proof: a termwise-injective unbounded complex need not be K-injective, so first replace `I`
by its functorial K-injective resolution `I ⟶ R(I)` with injective terms (Stacks 079P); its
localization is an isomorphism and naturality of the trace reduces to `R(I)`. There derived
coinduction at `Q R(I)` is ordinary coinduction applied termwise. Apply the degreewise
injective short exact sequence to obtain a short exact sequence of complexes. Identify its
mapping-cone projection with the normalized cone boundary using the augmentation adjoint
formula, then transpose along the derived coinduction adjunction. The resulting component
is invertible after localization.
-/
theorem reductionCoinductionTrace_isIso_onInjectiveTerms
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (I : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    [∀ i : ℤ, Injective (I.X i)] :
    IsIso ((reductionCoinductionTrace.{u} l E T n).app (DerivedCategory.Q.obj I)) := by
  sorry

end WeilConjectures
