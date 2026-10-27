/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.CoefficientRingedTensorHomModel
import all Sheaf.Paper.ConstantCompletionEquivalence
import all Sheaf.Paper.ConstantCompletionCore
import all Sheaf.Paper.IntegralTensorReductionTowerComparison

/-! # Normalized scalar comparison for finite total tensors

Source: Stacks Project, sites-modules.tex, Tag 03EL; sites-cohomology.tex, Tags 06YM, 07A4.
(blueprint: lem-sf-normalized-finite-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.ConstantCompletion
attribute [local irreducible] CategoryTheory.ConstantCompletion.completed
  CategoryTheory.ConstantCompletion.quotientPresentation HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.ConstantCompletion.rlim

namespace CategoryTheory.AmbientCompletedTensor

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] (I : Ideal A)

private theorem tensorGenerator_smul (R : Sheaf J CommRingCat.{u})
    (P Q : Cx R) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (a b : R.obj.obj U) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    coefficientTensorGenerator.{u, u, u} J R P Q p q k h U (a • x) (b • y) =
      (a * b) • coefficientTensorGenerator.{u, u, u} J R P Q p q k h U x y := by
  unfold coefficientTensorGenerator
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, smul_smul]
  rw [mul_comm]

/-- Scalar extension commutes with the direct-sum total tensor, with both scalar
factors recorded. The comparison sends (a*b) tensor (x tensor y) to
(a tensor x) tensor (b tensor y).
Source: Stacks 03EL, 06YM, 07A4.
(blueprint: lem-sf-normalized-finite-tensor-comparison).
Proof: apply the proved scalarTensorTotal isomorphism to the actual change-of-rings
functor and restrict scalars. Its normalization gives the formula for a=b=1.
Linearity of the comparison and bilinearity of the tensor generator give the
formula for arbitrary a and b. No flatness or nonzero-ring assumption is used. -/
theorem normalizedFiniteTensorComparison (n : ℕ)
    [(reduction J A I true n).Additive] :
    ∃ e : coefficientTotalTensor.{u, u, u} J (completed J A I) ⋙
        (reduction J A I true n).mapHomologicalComplex (.up ℤ) ≅
      ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
          ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
        coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
          (res (projection J A I n)).mapHomologicalComplex (.up ℤ),
      ∀ (P Q : Cx (completed J A I)) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (a b : (finite J A I n).obj.obj U)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((e.hom.app (P, Q)).f k).val.app U
          (tensorSection (projection J A I n)
            (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)).X k)
            U (a * b) (coefficientTensorGenerator.{u, u, u} J (completed J A I)
              P Q p q k h U x y)) =
          coefficientTensorGenerator.{u, u, u} J (finite J A I n)
            (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
            (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
            p q k h U (tensorSection (projection J A I n) (P.X p) U a x)
              (tensorSection (projection J A I n) (Q.X q) U b y) := by
  obtain ⟨e, he⟩ := WeilConjectures.scalarTensorTotal.{u, u, u}
    (projection J A I n) (change (projection J A I n)) (fun _ ↦ rfl) (fun _ ↦ rfl)
  refine ⟨Functor.isoWhiskerRight e
    ((res (projection J A I n)).mapHomologicalComplex (.up ℤ)), ?_⟩
  intro P Q p q k h U a b x y
  have hh := he P Q p q k h U x y
  change ((e.hom.app (P, Q)).f k).val.app U
      (tensorSection (projection J A I n) _ U 1
        (coefficientTensorGenerator.{u, u, u} J (completed J A I)
          P Q p q k h U x y)) =
    coefficientTensorGenerator.{u, u, u} J (finite J A I n)
            (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
            (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
            p q k h U (tensorSection (projection J A I n) (P.X p) U 1 x)
              (tensorSection (projection J A I n) (Q.X q) U 1 y) at hh
  change ((e.hom.app (P, Q)).f k).val.app U
    (tensorSection (projection J A I n) _ U (a * b) _) = _
  rw [tensorSection_smul, map_smul, hh]
  rw [tensorSection_smul (projection J A I n) (P.X p) U a x,
    tensorSection_smul (projection J A I n) (Q.X q) U b y]
  exact (tensorGenerator_smul J _ _ _ p q k h U a b _ _).symm

end CategoryTheory.AmbientCompletedTensor
