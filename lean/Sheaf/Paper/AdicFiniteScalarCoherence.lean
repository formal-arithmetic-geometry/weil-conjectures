/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.Paper.AdicFiniteRealizationData
import Sheaf.Paper.ScalarCompletionAssociator
import Sheaf.CategoryTheory.ModuleObjects.InternalTensorCompositionUnitNormalization

/-! # Scalar coherence of finite adic realizations

Source: BS Proposition 6.8.14(2); quotient comparison and balanced tensor normalization.
(blueprint: lem-sf-adic-finite-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicFiniteRealization
variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]

/-- The finite realization comparisons intertwine the specified raw associators and units.
Source: BS Proposition 6.8.14(2); finite realization node, steps 5--6
(blueprint: lem-sf-adic-finite-scalar-coherence).

Proof:
1. For each inclusion take rationalRealizationScalarCoherence for the two supplied
realizations. Its coefficient is the continuous-function inclusion, and its integral
normalization identifies both routes through the single derived tensor over B_E.
2. Identify pbcCompletedScalarMap with the finite-quotient coefficient inclusion by
uniqueness of the limit map. This gives completed_square. Conjugate the tensor theta
by the integral comparison of the literal-identity raw stage transition. Its component
on QK followed by J_F of that comparison has exactly the two single-tensor formulas
in ScalarData.integral. At equal fields it includes the actual multiplication unitor;
no heterogeneous equality of distinct tensor presentations is asserted.
3. Compose the actual field inclusions to obtain coefficient_comp. Substitute the
three normalized theta components into the tower equation. Use raw.coherence for
the inverse chi comparisons and the scalar-completion associator normalization.
The inner chi and its inverse cancel. The remaining tensor reassociations agree
by multiplication of the scalar factors on K-flat representatives. Naturality and
the fraction formulas extend the equation to all raw rational arrows.
4. For equal fields take the ordinary and derived multiplication unitors of
rationalRealizationScalarUnit. Their section and cochain equations give precisely
unit_normalization. raw.unit cancels the identity completion inverse; multiplication
by one leaves the actual framework unitor. This gives identity, also for repeated
fields and ramified inclusions. No essential-image or closure comparison is used. -/
theorem adic_finite_scalar_coherence (C : Core l T) :
    ∃ B : ScalarData l T C, Nonempty (Coherence l T C B) := by sorry

end WeilConjectures.AdicFiniteRealization
