/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeInverseBijective

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Every normalized affine degree comparison has a two-sided inverse.
Source: Stacks Project, Tag 03P2, affine calculation; Tags 01I9 and 01IA.

Compare tensor pullback with Mathlib pullback by uniqueness of the left
adjoint to the same pushforward, respecting their units. This transports
quasi-coherence of U*F from the Mathlib pullback theorem. -/
theorem exists_singletonTensorDegreeComparison_inverse
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    ∃ inv : (singletonTensorCech X F U W g).X n ⟶
      (singletonTensorAmitsur X F U W g).X n,
      f ≫ inv = 𝟙 _ ∧ inv ≫ f = 𝟙 _ := by
  have hb := singletonTensorDegreeComparisonHom_bijective X F U W g hU hW n f hf
  let e : (singletonTensorAmitsur X F U W g).X n ≃+
      (singletonTensorCech X F U W g).X n :=
    AddEquiv.ofBijective (AddCommGrpCat.Hom.hom f) hb
  let inv : (singletonTensorCech X F U W g).X n ⟶
      (singletonTensorAmitsur X F U W g).X n :=
    AddCommGrpCat.ofHom e.symm.toAddMonoidHom
  refine ⟨inv, ?_, ?_⟩
  · apply AddCommGrpCat.hom_ext
    ext x
    change e.symm (e x) = x
    simp
  · apply AddCommGrpCat.hom_ext
    ext x
    change e (e.symm x) = x
    simp

end
end AlgebraicGeometry.Scheme
