/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.PbcScalarTensor

/-! # Scalar tensor carries the output of the source completion reflector to a complete object.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    (W : Scheme.{u})

/-- Scalar tensor carries the output of the source completion reflector to a complete object.
Source: Stacks Project, Tags 099B and 0A0E; the finite-free scalar argument of
lem-weil-pbc-finite-free-completion-transport, steps 2--3.
(blueprint: lem-pbc-scalar-completed-object-complete).

Proof: transport the completed coefficient map through pbcCompletedComparison, which
is fixed on every finite quotient. The target integer ring is finite free over the
source integer ring; the same finite basis, applied to continuous sections and then
to the quotient limit, makes the target coefficient sheaf finite free. Restricting
its derived scalar extension gives a finite direct sum of the original complex.
The source completion output is intrinsically complete by the reflector property.
The complete subcategory is closed under finite sums, including the empty sum.
Exact scalar restriction identifies the source-parameter Koszul tower with the
Koszul tower for its image in the target ring. This image is a unit times a positive
power of the target uniformizer. The two principal ideals therefore have cofinal
powers, giving the same local derived completeness predicate by the unit-power
criterion. Transport back through the normalized coefficient presentation. This
proves precisely target completeness of scalar tensor of the completion output;
no scalar/completion comparison is used. -/
theorem pbcScalarCompletedObjectComplete (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i W).obj
        ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) := by sorry

end AlgebraicGeometry.Scheme
