/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorModels

/-! # Descent of the integral point tensor augmentation

Source: Stacks 07A4, 0941 and 031B.
(blueprint: lem-sf-point-integral-tensor-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Descend a normalized chain augmentation to the completed tensor on constructible
objects; the conclusion concerns only the derived tensor and unit constraints.
Source: Stacks 07A4, 0941 and 031B, integral point comparison proof step 2
(blueprint: lem-sf-point-integral-tensor-descent).

Proof: the two coordinate hypotheses determine the augmentation on every total
summand and hence determine the whole chain map. Point sections is exact and
preserves countable products, so the specified Roos comparison carries this map
to the ordinary quotient coaugmentation. The reduction comparison identifies its
finite coordinates with reductions of the ordinary tensor. Bounded finite
cohomology of constructible point sections and DVR perfectness give bounded
finite-projective models; perfectTensorRoosCompletion makes their quotient
coaugmentation a quasi-isomorphism. This gives the inverse derived tensorator.
Tensor preserves constructibility and finite Tor amplitude. Transport the ordinary
signed associativity, symmetry and unit constraints to this completed tensor:
their diagrams commute after the quotient coordinates and zero shifted coordinate,
then after localization. The tensor functor and unit are the specified ones,
so the resulting monoidal structure has tensor_eq and unit_eq by construction.
The tensorator normalization is precisely the localized augmentation. On the
coefficient unit, constant sections identify its degree-zero sections with the
coefficient ring and give the displayed unit model. No choices of unconstrained
completion maps occur. -/
theorem pointIntegralTensorDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (completion : pointIntegralTensorCompletion D l E)
    (hfirst : PointIntegralTensorFirst D l E completion)
    (hsecond : PointIntegralTensorSecond D l E completion) :
    ∃ S : PointIntegralTensorData D l hl E,
      PointIntegralTensorComparison D l hl E S completion ∧
        PointIntegralTensorUnitModel D l hl E S := by
  sorry

end WeilConjectures
