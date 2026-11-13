/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentation
public import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorSquare
import WeilConjectures.AlgebraicGeometry.TensorConeTowerIso

/-! # Tensor of the normalized coefficient augmentation cone

## References

* Stacks Project, Tags 099M, 093M and 0A0E
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local instance] flatConstantCochainMonoidal flatConstantCochainMonoidalStruct

/-- Tensoring the coefficient cone gives the actual cone at an arbitrary complex.
This is a strict tower isomorphism, with no Noetherianity, flatness, localization,
or inverse-limit assertion (Stacks, Tags 099M and 06YP). -/
theorem constantKoszulTensorConeComparison
    (b : Bool) (r : ℕ) (a : Fin r → A)
    (α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ))
    (hα : KoszulQuotientAugmentationLaws J A I b r a α)
    (P : Cx (coefficients J A I b)) :
    Nonempty
      ((CochainComplex.mappingCone
          (α.app (ringedSiteRingComplex (coefficients J A I b)))).asFunctor ⋙
        tensorLeft P ≅ (CochainComplex.mappingCone (α.app P)).asFunctor) := by
  let := SheafOfModules.monoidalCategory (coefficients J A I b)
  let O := coefficients J A I b
  let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
  let U := ringedSiteRingComplex O
  let β := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app U)
  let γ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app P)
  obtain ⟨e, he⟩ := constantReductionTensorModel J A I b
  let E := Functor.isoWhiskerRight
    (KoszulTensorComparison.reductionModelIso J A I b e U) (tensorLeft P) ≪≫
    TensorComparison.tensorTowerComparison J O ((reductionTower J A I b).obj (𝟙_ (Mod O))) P ≪≫
    (KoszulTensorComparison.reductionModelIso J A I b e P).symm
  have h := KoszulTensorComparison.augmentationTensorSquare J A I b r a α hα e he P
  exact tensorConeTowerIso (curriedTensor (Mod O)) P (α.app U) (α.app P)
    (KoszulTensorComparison.koszulSourceTensorIso J O r s P) E h

end CategoryTheory.ConstantCompletion
