/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.IntegralComparisonSystemData

/-! # Ambient normalized primitive comparison data

Source: Stacks 099N(2),(5), 06YY, 0941; the quotient-diagram construction in
blueprint trace transport (blueprint: lem-trf-ambient-comparison-system-existence).
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures

/-- Primitive normalized realization data exist on every scheme, with effectivity
on the constructible domain recorded by the comparison interface.
Source: Stacks 099N(2),(5), 06YY and 0941; blueprint common-stage transport,
construction of the strict quotient models
(blueprint: lem-trf-ambient-comparison-system-existence).

Proof: for each coefficient field and scheme take the whole-system derived reduction
adjunction with its quotient evaluation comparisons. The right-derived restriction
and limit construction supplies its natural Roos comparison, normalized on every
K-injective tower by the ordinary cone. On a flat-term K-flat representative, whole
system pullback of its reduction is the diagram of the pulled-back finite quotient
complexes. Its Roos realization is the defining completed pullback. Derived change
of rings similarly identifies scalar change of reduction with the diagram of the
scalar quotient tensors; the balanced association multiplies the two coefficient
factors and retains all quotient transitions. These constructions are available
without inverting ell on the base scheme: they concern module sheaves and the
actual quotient coefficient maps. Descent along K-flat resolutions gives the two
normalized primitive models on the ambient categories. For a constructible complete
input, normalized reconstruction makes the actual unit invertible. Its counit on
the scalarized reduction is invertible by the same normalized quotient tensor
calculation. With ell invertible on both schemes, the pullback calculation and
constructibility preservation give invertibility of its pullback counit as well.
Choose these constructions simultaneously over all the field and scheme parameters.
This proves existence of the primitive data only; no mixed, scalar-unit, scalar-tower
or geometric coherence equation is asserted here. -/
theorem ambientComparisonSystem_exists (l : ℕ) [Fact l.Prime] :
    Nonempty (IntegralComparisonSystem.{u} l) := by
  sorry

end WeilConjectures
