/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Acyclicity in a tensored cone sequence

Source: Stacks Project, sites-cohomology.tex, Lemma 07A3, with the cone of Definition 06YN
(blueprint: lem-pc-kflat-tensor-cone-two-out-of-three).
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- A local abbreviation for the existing category of modules over the ring sheaf. -/
private abbrev moduleCategory :=
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
        (A.mapBifunctor K₁ (curriedTensor (moduleCategory R))).Acyclic) := sorry

end SheafOfModules
