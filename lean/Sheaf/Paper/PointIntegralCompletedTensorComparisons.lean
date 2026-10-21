/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorCompatibility
/-! # Completed integral tensor at the geometric point

Source: Stacks 0941, 031B and 07A4.
(blueprint: lem-sf-point-integral-completed-tensor-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- The completed integral point comparison with both Roos coordinates and all
coefficient-embedding squares normalized.
Source: Stacks 0941, 031B and 07A4
(blueprint: lem-sf-point-integral-completed-tensor-comparisons).

Proof: the finiteness theorem gives bounded finitely generated cohomology for the
point fibre. Over the coefficient DVR these complexes are perfect. Replace them
by bounded finite-projective complexes. Their tensor is again of this form; each
term is complete as a direct summand of a finite free module. Quotient transitions
are surjective, and the kernel of one minus transition on the product is the
original term. Thus the normalized augmentation to its Roos complex is a
quasi-isomorphism. Exact evaluation preserves products and the shifted cone, with
both coordinates and the augmentation fixed. The point reduction comparison
identifies the tensor tower with the quotient tower of the ordinary tensor.
Compose the resulting identification with the inverse completion augmentation.
Its first coordinate is the quotient tensor generator and its second coordinate
is zero. Associativity, signed symmetry and the coefficient-unit identities hold
on the ordinary tensor models and therefore after completion and localization.
Integral tensor preserves constructibility and finite Tor amplitude, giving the
source subcategory. For a coefficient embedding, use the recorded scalar chain
map. On the first coordinate both paths multiply the two coefficients; on the
shifted coordinate both are zero. The scalar/completion theorem and naturality
then give the asserted square, including identity embeddings. -/
theorem pointIntegralCompletedTensorComparisons
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    ∃ I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E,
      ∃ C : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
        [FiniteDimensional ℚ_[l] E], PointIntegralTensorCanonical D l hl E (I E),
        ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
          [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
          [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
          PointIntegralTensorScalarSquare D l hl E L ι (I E) (I L) (C E) (C L) := by
  sorry

end WeilConjectures
