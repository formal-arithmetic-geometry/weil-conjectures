/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Acyclicity in a tensored cone sequence

Source: Stacks Project, sites-cohomology.tex, Lemma 07A3, with the cone of Definition 06YN
(blueprint: lem-pc-kflat-tensor-cone-two-out-of-three).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- A local abbreviation for the existing category of modules over the ring sheaf. -/
abbrev moduleCategory :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

noncomputable local instance : MonoidalCategory (moduleCategory R) := monoidalCategory R

/-- (blueprint: lem-pc-kflat-tensor-cone-two-out-of-three) Stacks Project, Lemma 07A3.
The cone comparison for the total tensor complex identifies tensoring the cone of `f`
with the cone of the induced tensor map. The cone triangle is distinguished in the
homotopy category; since acyclic complexes form a triangulated subcategory, any two
acyclic total tensor complexes force the third to be acyclic. -/
theorem tensor_mappingCone_two_out_of_three :
    ∀ (A K₁ K₂ : CochainComplex (moduleCategory R) ℤ) (f : K₁ ⟶ K₂),
      A.Acyclic →
      (∃ e : CochainComplex.mapBifunctor A (CochainComplex.mappingCone f)
          (curriedTensor (moduleCategory R)) ≅
          CochainComplex.mappingCone
            (HomologicalComplex.mapBifunctorMap (𝟙 A) f (curriedTensor (moduleCategory R)) (.up ℤ)),
        HomologicalComplex.mapBifunctorMap (𝟙 A) (CochainComplex.mappingCone.inr f)
            (curriedTensor (moduleCategory R)) (.up ℤ) ≫ e.hom =
          CochainComplex.mappingCone.inr
            (HomologicalComplex.mapBifunctorMap (𝟙 A) f
              (curriedTensor (moduleCategory R)) (.up ℤ))) ∧
      ((A.mapBifunctor K₁ (curriedTensor (moduleCategory R))).Acyclic ∧
          (A.mapBifunctor K₂ (curriedTensor (moduleCategory R))).Acyclic →
        (A.mapBifunctor (CochainComplex.mappingCone f)
          (curriedTensor (moduleCategory R))).Acyclic) ∧
      ((A.mapBifunctor K₁ (curriedTensor (moduleCategory R))).Acyclic ∧
          (A.mapBifunctor (CochainComplex.mappingCone f)
            (curriedTensor (moduleCategory R))).Acyclic →
        (A.mapBifunctor K₂ (curriedTensor (moduleCategory R))).Acyclic) ∧
      ((A.mapBifunctor K₂ (curriedTensor (moduleCategory R))).Acyclic ∧
          (A.mapBifunctor (CochainComplex.mappingCone f)
            (curriedTensor (moduleCategory R))).Acyclic →
        (A.mapBifunctor K₁ (curriedTensor (moduleCategory R))).Acyclic) := by
  intro A K₁ K₂ f hA
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor R
  let (M : moduleCategory R) := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj R M
  let e := CochainComplex.mapBifunctorMappingCone₂Iso A f
    (curriedTensor (moduleCategory R))
  let g := HomologicalComplex.mapBifunctorMap (𝟙 A) f
    (curriedTensor (moduleCategory R)) (.up ℤ)
  let P := HomotopyCategory.subcategoryAcyclic (moduleCategory R)
  have hmem (K : CochainComplex (moduleCategory R) ℤ) :=
    HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K
  have he : (A.mapBifunctor (CochainComplex.mappingCone f)
      (curriedTensor (moduleCategory R))).Acyclic ↔
      (CochainComplex.mappingCone g).Acyclic := by
    rw [← hmem, ← hmem]
    exact P.prop_iff_of_iso ((HomotopyCategory.quotient _ _).mapIso e)
  have hd := HomotopyCategory.mappingCone_triangleh_distinguished g
  refine ⟨⟨e, ?_⟩, ?_, ?_, ?_⟩
  · exact CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom A f
      (curriedTensor (moduleCategory R))
  · rintro ⟨h₁, h₂⟩
    apply he.mpr
    apply (hmem _).mp
    exact P.ext_of_isTriangulatedClosed₃ _ hd ((hmem _).mpr h₁) ((hmem _).mpr h₂)
  · rintro ⟨h₁, h₃⟩
    apply (hmem _).mp
    exact P.ext_of_isTriangulatedClosed₂ _ hd ((hmem _).mpr h₁)
      ((hmem _).mpr (he.mp h₃))
  · rintro ⟨h₂, h₃⟩
    apply (hmem _).mp
    exact P.ext_of_isTriangulatedClosed₁ _ hd ((hmem _).mpr h₂)
      ((hmem _).mpr (he.mp h₃))

end SheafOfModules
