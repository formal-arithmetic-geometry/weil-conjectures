/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstantSemilinearGeneratorComparison
import WeilConjectures.SixFunctors.IntegralConstantCompleteTransportComplete
import WeilConjectures.SixFunctors.IntegralConstantCompleteTransportHom

/-! # Complete integral objects in constant coefficient coordinates

Source: Stacks Tags 099I and 099M; the coefficient transport in the integral
compactification bridge (blueprint: lem-sf-integral-constant-complete-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction

/-- Constant restriction carries integral constructible objects to complete objects
and induces a bijection on their ambient Hom sets.

Source: Stacks Tags 099I, 099M; integral compactification bridge, Steps 1 and 8
(blueprint: lem-sf-integral-constant-complete-transport).

Proof: identify the coefficient quotient tower with the powers of the uniformizer
ideal using the canonical quotient ring isomorphisms, including the transition maps.
The Roos-unit condition defining IsSfDerivedComplete is therefore the derived
completion condition for that ideal. Transport this condition through the exact
small-site module equivalence. The constant-completion equivalence, whose ambient
functor is restriction along the specified coefficient map, carries these complete
objects to complete constant-coefficient objects and is fully faithful on them.
The derived comparison for a composite of exact functors identifies this ambient
restriction with H. Conjugating its Hom bijection by that comparison yields the
asserted bijection for H.map itself. Neither a Tor bound nor a finite-field datum
is used. Zero objects and the empty site use the same Roos triangle and equivalence. -/
theorem integralConstantCompleteTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    (∀ K : sfIntegralConstructibleCategory l E X,
      (sfCbcSite X).IsComplete _ (sfCbcModelIdeal (constantDatum l E))
        ((H l E X).obj K.obj)) ∧
    (∀ K L : sfIntegralConstructibleCategory l E X,
      Function.Bijective (fun m : K.obj ⟶ L.obj ↦ (H l E X).map m)) := by
  constructor
  · intro K
    exact integralConstantCompleteTransport_complete l E X K
  · intro K L
    exact integralConstantCompleteTransport_hom l E X K L

end WeilConjectures.GeneratorReduction
