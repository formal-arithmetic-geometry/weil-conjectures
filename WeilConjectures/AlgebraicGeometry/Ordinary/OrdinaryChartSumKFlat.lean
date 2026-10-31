/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCoefficientComputation
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumTensorTotalization

/-! # Etale summation preserves native K-flat complexes

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-sum-kflat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
section
variable {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalPreadditive C]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

private theorem tensor_acyclic_of_kFlat (P H : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) (hH : H.Acyclic) :
    (CochainComplex.mapBifunctor P H (curriedTensor C)).Acyclic := by
  have ht := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1
    ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
    ((HomotopyCategory.quotient C (.up ℤ)).obj H)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic H).2 hH)
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 ht.1

private theorem kFlat_of_tensor_acyclic (P : CochainComplex C ℤ)
    (h : ∀ H : CochainComplex C ℤ, H.Acyclic →
      (CochainComplex.mapBifunctor P H (curriedTensor C)).Acyclic) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro H hH
  obtain ⟨H, rfl⟩ := H.quotient_obj_surjective
  have ht := h H
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic H).1 hH)
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 ht
  exact ⟨hr, (HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr⟩
variable {D : Type*} [Category D] [Abelian D] [MonoidalCategory D]
  [SymmetricCategory D] [MonoidalPreadditive D]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

private theorem kFlat_map_of_comparison
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    (hL : ∀ P : CochainComplex C ℤ, P.Acyclic →
      ((L.mapHomologicalComplex (.up ℤ)).obj P).Acyclic)
    (hR : ∀ H : CochainComplex D ℤ, H.Acyclic →
      ((R.mapHomologicalComplex (.up ℤ)).obj H).Acyclic)
    (Ψ : AlgebraicGeometry.TotalTensorComparison (curriedTensor C) (curriedTensor D) L R)
    (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply kFlat_of_tensor_acyclic
  intro H hH
  have hT := tensor_acyclic_of_kFlat P
    ((R.mapHomologicalComplex (.up ℤ)).obj H) hP (hR H hH)
  have hLT := hL _ hT
  intro n
  exact (hLT n).of_iso (Ψ P H).symm

end

namespace AlgebraicGeometry.Etale
attribute [local irreducible] etaleLowerShriek upperStar

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- Etale summation preserves native K-flat complexes.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-sum-kflat).

Proof: Use the characterization of K-flatness by acyclicity after tensoring with every acyclic
complex, passing between complexes and the homotopy category.
Pull an acyclic target complex back along the exact inverse-image functor. Tensor with the source
K-flat complex and then apply exact summation; the result is acyclic.
The total-tensor projection comparison identifies that result with the tensor of the summed
complex and the original target complex. Transport acyclicity through this isomorphism and apply
the characterization of K-flatness. -/
theorem ordinaryChartSumKFlat
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (f : U ⟶ X) [hf : AlgebraicGeometry.Etale f]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((etaleLowerShriek (ModuleCat.{u + 1} A) f hf).mapHomologicalComplex
        (.up ℤ)).obj P) := by
  let L := etaleLowerShriek (ModuleCat.{u + 1} A) f hf
  let R := upperStar (ModuleCat.{u + 1} A) f
  obtain ⟨Ψ⟩ := AlgebraicGeometry.etale_sum_tensor_comparison A f hf
  exact kFlat_map_of_comparison L R
    (fun _ h n ↦ (h n).map L) (fun _ h n ↦ (h n).map R) Ψ P hP

end AlgebraicGeometry.Etale
