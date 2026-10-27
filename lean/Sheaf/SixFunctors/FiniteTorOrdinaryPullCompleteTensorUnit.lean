/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.Paper.DerivedCompleteOnSlices
import all Sheaf.SixFunctors.OpenReconstructionEffectivity

/-! # Completeness of the integral tensor unit

Source: Bhatt--Scholze, Lemma 6.5.5; Stacks Project, Tags 099I and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The integral tensor unit is derived complete on every scheme.

Source: Bhatt--Scholze, Lemma 6.5.5 and Stacks Tags 099I, 0941.
Proof: the regular completed coefficient sheaf is the inverse limit of its
surjective quotient tower. The rank-one free model gives the canonical Roos
triangle with the prescribed quotient augmentations, including the empty and
zero cases.
(blueprint: lem-sf-finite-tor-ordinary-pull-complete-tensor-unit). -/
theorem tensorUnit_complete_for_finiteTorOrdinaryPull (Y : Scheme.{u}) :
    IntegralOnSlice.IsComplete l E Y none
      (IntegralSystemRealization.calculus l E Y).integralClosed.monoidal.tensorUnit := by
  exact tensorUnit_complete l E Y

end WeilConjectures.GeneratorReduction
