/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensor

/-! # Independence of normalized rational point tensor comparisons

Source: retained point-pairing argument, Step 1.
(blueprint: lem-pod-point-tensor-normalization-independent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Canonical normalization fixes the rational tensor map independently of the closure.
Source: retained point-pairing proof Step 1, and the specified finite pure-tensor,
integral Roos and rational localization normalizations.
(blueprint: lem-pod-point-tensor-normalization-independent).
Proof: on finite K-flat models, both comparisons send each sheaf tensor generator
to the tensor of its two sections. These generators span, so the chain maps agree.
The integral normalizations are the inverse completed augmentations of these maps:
the quotient tensor is their first Roos coordinate and the second coordinate is
zero. The specified maps of products and shifted cones therefore coincide before
localization; no faithfulness of individual finite reductions is invoked.
The rational normalization is their image under the balanced scalar tensorator,
with the specified scalar counit. The coefficient/carrier lift is normalized on
pure tensors as well, so its tensorators coincide on complexes and hence on
roofs. Faithfulness of the carrier lift reflects equality of the rational maps.
The closure is absent from this computation at E, giving the claimed independence.
Zero inputs give the unique map between zero objects; no shifts are excluded. -/
theorem point_tensor_normalization_independent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω₁ : Type u) [Field Ω₁] [Algebra ℚ_[l] Ω₁] [IsAlgClosure ℚ_[l] Ω₁]
    (Ω₂ : Type u) [Field Ω₂] [Algebra ℚ_[l] Ω₂] [IsAlgClosure ℚ_[l] Ω₂]
    (S₁ : PointFibreDerivedTensorSystem D l hl Ω₁)
    (S₂ : PointFibreDerivedTensorSystem D l hl Ω₂)
    (h₁ : Nonempty (PointFibreDerivedTensorCanonical D l hl Ω₁ S₁))
    (h₂ : Nonempty (PointFibreDerivedTensorCanonical D l hl Ω₂ S₂))
    (M N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    HEq ((S₁.rational E).tensorIso M N).hom ((S₂.rational E).tensorIso M N).hom := by
  sorry

end WeilConjectures
