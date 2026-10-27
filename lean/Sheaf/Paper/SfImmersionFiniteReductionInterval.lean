/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SfImmersionCompletedPullbackCoreA

/-! # Finite reductions of ordinary immersion pullback

Source: localization Step 6, finite constructibility; Stacks Tags 09AK, 09AL and 09B5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme.ImmersionCompletedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- One finite reduction retains constructibility and the given interval under pullback.
Source: localization Step 6, last paragraph, and Stacks Tags 09AK, 09AL and 09B5
(blueprint: lem-sf-immersion-finite-reduction-interval).

Proof: identify the two quotient coefficient rings by quotientEquiv and the completed
coefficients by completedRingIso, retaining their projection equations. The scalar
extension adjunctions then identify detailed reduction of transport with the canonical
finite reduction of the adic datum. Compose this identification with finiteComparison:
the target reduction is the exact inverse image of the source reduction, up to these
coefficient equivalences. Exact coefficient restriction preserves and reflects zero
cohomology and finite locally constant module sheaves on every stratum. Exact inverse
image commutes with cohomology; pull back the finite locally closed stratification of
each source cohomology sheaf and its finite constant local models. Thus each target
cohomology sheaf is constructible. In every degree outside [r,s] the source cohomology
is zero, hence so is its inverse image. The target support is therefore contained in
the same interval, which is finite; this also supplies the finite-support clause of
intrinsicFiniteTorsionConstructible. This argument uses no Noetherian assumption and
includes the zero complex, an empty interval, the empty scheme, and identity immersion.
-/
theorem finite_reduction_preservesConstructibleInterval [IsImmersion f]
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) (r s : ℤ)
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj ((transport l E X).obj K)) ∧
      proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj ((transport l E X).obj K)) ⊆
          Set.Icc r s) :
    intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ∧
      proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ⊆
        Set.Icc r s := by sorry

end AlgebraicGeometry.Scheme.ImmersionCompletedPullback
