/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstantSemilinearGeneratorComparison

/-! # Pointwise Hom transport for integral constant coordinates

Source: Stacks Tags 099I and 099M; coefficient transport in the integral
compactification bridge (blueprint: lem-sf-integral-constant-complete-transport-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction

/-- Restriction along the constant coefficient map is bijective on one pair of
integral constructible inputs.

Source: Stacks Tags 099I and 099M, specialized to the fixed quotient tower.
Proof: the constant and completed quotient towers are identified term by term.
The exact small-site equivalence and the completion reflector identify the two
Hom sets; conjugating by the canonical derived comparison gives precisely the
map of `H`.  The inverse and both cancellation identities are transported from
the completion Hom equivalence, with no finite-field or Tor hypotheses.
(blueprint: lem-sf-integral-constant-complete-transport-hom).
-/
theorem integralConstantCompleteTransport_hom
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K L : sfIntegralConstructibleCategory l E X) :
    Function.Bijective (fun m : K.obj ⟶ L.obj ↦ (H l E X).map m) := by
  sorry

end WeilConjectures.GeneratorReduction
