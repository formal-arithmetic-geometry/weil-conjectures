/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! # Triangle identity for common-stage tensor

Source: Stacks Project, Tags 07A4 and 0941; the coefficient-stage conventions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The prescribed common-stage associator and unitors satisfy the triangle identity.

Source: Stacks Project, Tags 07A4 and 0941; the normalized coefficient tensor
constraints of `lem-pur-derived-pullback-tensor-constraints`.
(blueprint: lem-pur-common-stage-tensor-triangle).

Proof: apply faithful coherent reduction to the integral equation and insert
the prescribed tensor comparison and the reduction of the reconstructed unit.
Naturality of the tensor comparison cancels the inner comparison maps. The
remaining equation is precisely the monoidal triangle identity for the selected
coherent-system monoidal structure. No normalization of its associator on
cochain representatives or compatibility with a separate signed braiding is
needed. Localize this equality to each rational coefficient field using the
defining representatives of the rational associator and both unitors. For the
common-stage equation, choose a finite field containing the stages of both
inputs, the unit, and all intermediate tensor objects. The prescribed
common-stage representatives conjugate the rational associator and unitors by
the same tensor comparisons. Tensor naturality cancels these comparisons and
the unit-stage isomorphism; the rational triangle identity makes the resulting
representatives equal. Their classes are therefore equal. Zero objects and
an empty scheme require no additional hypothesis. -/
theorem commonStageTensor_triangle
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (pullbackTensorCommonAssociator l Ω X A (pullbackTensorCommonUnit l Ω X) B).hom ≫
        (commonStageDerivedTensor l Ω X).map
          (Prod.mkHom (𝟙 A) (pullbackTensorCommonLeftUnitor l Ω X B).hom) =
      (commonStageDerivedTensor l Ω X).map
        (Prod.mkHom (pullbackTensorCommonRightUnitor l Ω X A).hom (𝟙 B)) := by
  sorry

end WeilConjectures
