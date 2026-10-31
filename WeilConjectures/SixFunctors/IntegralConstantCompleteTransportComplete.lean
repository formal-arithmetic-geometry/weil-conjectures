/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstantSemilinearGeneratorComparison

/-! # Pointwise completeness transport for integral constant coordinates

Source: Stacks Tags 099I and 099M; coefficient transport in the integral
compactification bridge (blueprint: lem-sf-integral-constant-complete-transport-complete).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction

/-- The constant restriction of one integral constructible input is complete.

Source: Stacks Tags 099I and 099M, specialized to the fixed quotient tower.
Proof: identify the positive coefficient quotients with the powers of the
uniformizer ideal.  The Roos unit criterion is invariant under the exact
small-site module transport, and the constant-completion restriction is the
specified functor `H`.  The transported Roos triangle is therefore the local
`IsComplete` witness on the target site, including the zero and empty-site cases.
(blueprint: lem-sf-integral-constant-complete-transport-complete).
-/
theorem integralConstantCompleteTransport_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    (sfCbcSite X).IsComplete _ (sfCbcModelIdeal (constantDatum l E))
      ((H l E X).obj K.obj) := by
  sorry

end WeilConjectures.GeneratorReduction
