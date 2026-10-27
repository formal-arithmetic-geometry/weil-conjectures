/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices

/-! # Completion inverts the integral quotient unit

Source: Stacks Project, proetale.tex, Tag 099M; algebraization.tex, Tags 099B and 0A0E.
(blueprint: lem-sf-integral-completion-unit-inverted).
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory
namespace WeilConjectures.IntegralOnSlice

/-- Applying quotient completion to its own specified quotient unit gives an isomorphism.
This assertion concerns the completion functor on one arbitrary ambient input, without
any tensor product or complete target.
Source: Stacks 099M, 099B, 0A0E.
(blueprint: lem-sf-integral-completion-unit-inverted).
Proof: pass from the essentially small pro-etale site to its small model in coefficient
universe max(u,t+1). The principal uniformizer datum identifies the quotient tower
with the principal Koszul tower: its two-term free resolution maps to the actual
quotient by the original quotient augmentation, and these maps preserve every
transition and the degree-zero unit. Exact products identify their derived limits
with the specified Roos model. The resulting comparison of completion functors
therefore preserves their units. Koszul completion is the reflector onto locally
derived complete objects, and a reflector inverts its unit. Transport this
invertibility through the unit-preserving comparison and the site equivalence.
No boundedness or constructibility of the input is used. -/
theorem integralCompletion_unit_inverted
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (M : D.{t, u} l E X none) :
    IsIso ((completion.{t, u} l E X none).map
      ((completionUnit.{t, u} l E X none).app M)) := by sorry

end WeilConjectures.IntegralOnSlice
