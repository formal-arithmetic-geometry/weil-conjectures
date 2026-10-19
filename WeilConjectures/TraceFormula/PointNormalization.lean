/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClass

/-!

# Point normalization of the trace class

Over the base point `s = Spec k`, the trace class of the diagonal correspondence of an
endomorphism `v` of a dualizable object integrates to the categorical trace of `v` (blueprint
`prop-trf-pairing-point-normalization`, `sk-p-pairing`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace Correspondence

/-- **Point normalization of the pairing** (blueprint `prop-trf-pairing-point-normalization`,
`sk-p-pairing`): over the base point, the trace class of the diagonal correspondence of an
endomorphism `v` of a perfect complex integrates to the categorical trace of `v`,
`∫_s Tr(v) = tr(v)`. -/
theorem integral_traceClass_ofEnd {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    [HasRightDual K] (v : K ⟶ K) :
    ((ofEnd K v).traceClass (fixedLocusOfEnd v)).integral = trace v :=
  sorry

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
