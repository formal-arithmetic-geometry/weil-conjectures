/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.PurTwistCoefficientRings
import Sheaf.Paper.PurTwistCoefficientTensor
import Sheaf.CategoryTheory.SectionwisePushout
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The coefficient pushout comparison

Source: coefficient-twist blueprint, proof step 6.
(blueprint: lem-pur-twist-coefficient-comparison)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- The normalized scalar square is a pushout of ring sheaves.

Source: coefficient-twist blueprint, proof step 6; Stacks Project, Tag 03EK.
(blueprint: lem-pur-twist-coefficient-comparison)

Proof: the sectionwise balanced tensor map is bijective. It identifies the usual
commutative-ring tensor pushout with the square of sections. These sectionwise
pushouts imply a pushout among sheaves. The canonical map between its vertex and
the chosen categorical pushout is consequently an isomorphism. -/
theorem purTwistCoefficientComparison_isIso (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsIso (purTwistCoefficientComparison S l E) := by
  classical
  have hp : IsPushout (purTwistConstantIntegersMap S l E)
      (purTwistZlCompletionMap S l) (purTwistIntegralCompletionMap S l E)
      (purTwistCompletedScalarMap S l E) := by
    apply sheaf_isPushout_of_sectionwise (ProEt.topology S) _ _ _ _
      (purTwistCoefficientSquare S l E).symm
    intro U
    let R := (purTwistZlConstant S l).obj.obj U
    let A := (purTwistIntegralConstant S l E).obj.obj U
    let B := (purTwistZlCompletion S l).obj.obj U
    let : Algebra R A := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
    let : Algebra R B := ((purTwistZlCompletionMap S l).hom.app U).hom.toAlgebra
    let e := (RingEquiv.ofBijective (purTwistCoefficientTensorMap S l E U)
      (purTwistCoefficientTensor S l E U)).toCommRingCatIso
    apply (CommRingCat.isPushout_tensorProduct R A B).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    · rfl
    · rfl
    · ext x
      change ((purTwistIntegralCompletionMap S l E).hom.app U) x *
        ((purTwistCompletedScalarMap S l E).hom.app U) 1 = _
      rw [map_one, mul_one]
      rfl
    · ext x
      change ((purTwistIntegralCompletionMap S l E).hom.app U) 1 *
        ((purTwistCompletedScalarMap S l E).hom.app U) x = _
      rw [map_one, one_mul]
      rfl
  have he : hp.flip.isoPushout.hom ≫ purTwistCoefficientComparison S l E = 𝟙 _ := by
    apply hp.flip.hom_ext <;> simp [purTwistCoefficientComparison]
  have h' : purTwistCoefficientComparison S l E = hp.flip.isoPushout.inv := by
    rw [← cancel_epi hp.flip.isoPushout.hom, he, Iso.hom_inv_id]
  rw [h']
  infer_instance

end AlgebraicGeometry.Scheme
