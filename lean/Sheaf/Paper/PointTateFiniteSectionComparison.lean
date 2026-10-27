/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PointTateFiberComparisonData

/-! # Finite reduction of point Tate section modules

Source: coefficient comparison lemma, step 2.
(blueprint: lem-pur-point-tate-finite-section-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures.PointTateFiber

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]

/-- Sections of the normalized signed sheaf reduction are ordinary coefficient tensor.

Source: the coefficient comparison lemma, step 2; Deligne, Weil II (1.1.3), p. 150.
(blueprint: lem-pur-point-tate-finite-section-comparison).

Proof: choose compatible primitive roots and use point_tate_root_coordinates to
trivialize the integral and residue signed sheaves. In these coordinates the
normalized reduction sends c times the integral generator to its residue times
the finite generator. In degree zero this is the coefficient quotient; in degree
one it is the defining root tensor quotient; tensor induction proves it for
positive degrees. For a negative degree evaluate the dual comparison on the
positive basis, giving the same coefficient quotient by the signed reduction
normalization. Evaluation at the terminal object identifies the two coefficient
units with the actual integer ring and its positive quotient. The induced map on
a tensor a tensor (c times the integral generator) is a times residue(c) times
the residue generator. Its inverse sends a times the residue generator to
 a tensor the integral generator. Tensor balancing proves the inverse equations
for arbitrary quotient rings; no reducedness or field property is used. The
resulting isomorphism is independent of the root basis, because its pure-tensor
formula refers to the fixed reduction map and pure tensors generate. -/
theorem finiteSectionComparison (hl : l ≠ D.p) :
    ∃ z : FiniteComparisons D l,
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (n : ℕ) (m : ℤ)
        (a : Padic.coefficientExtensionRing l F (n + 1)) (x : integral D l F m),
      (z F n m).hom (a ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (n + 1))] x) =
        a • (@id (finite D l F n m)
          ((reduction D l F hl n m).val.app (finalObject D) x))) := by sorry

end WeilConjectures.PointTateFiber
