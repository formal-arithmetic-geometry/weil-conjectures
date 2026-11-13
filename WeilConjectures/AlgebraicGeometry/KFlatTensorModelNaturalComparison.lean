/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison

/-! # Natural tensor comparison with a fixed K-flat model

## References

* Stacks Project, Tag 06YH.
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

-- The natural comparison specializes the unbounded total-tensor bifunctor.
/-- The localization comparison is a natural isomorphism for a fixed K-flat
first complex and arbitrary second complexes. -/
theorem kFlat_tensorModel_naturalComparison (X : Scheme.{uX})
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    Nonempty
      (DerivedCategory.Q ⋙ (curriedTensor (schemeDerivedCategory X)).obj
        (DerivedCategory.Q.obj P) ≅
        ((curriedTensor
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace))).map₂CochainComplex.obj P) ⋙
            DerivedCategory.Q) := by
  classical
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  obtain ⟨e⟩ := kFlat_derivedTensor_comparison_natIso.{uX, wD} X
    ((Functor.const (Discrete PUnit.{1})).obj P) (𝟭 (CochainComplex C ℤ)) (fun _ ↦ hP)
  exact ⟨e.app ⟨PUnit.unit⟩⟩

end AlgebraicGeometry.Scheme
