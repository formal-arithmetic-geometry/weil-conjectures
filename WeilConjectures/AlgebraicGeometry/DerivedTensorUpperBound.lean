/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Derived tensor preserves an upper cohomological bound

## References

* Stacks Project, Tags 08EV, 06YS and 06YD
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry

/-- Tensoring a derived object with a module in degree zero preserves its upper bound
(Stacks, Tags 08EV, 06YS and 06YD). -/
theorem schemeDerivedTensorCohomologyVanishes_of_upper_bound
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (b : ℤ)
    (hE : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) (hi : b < i) :
    schemeDerivedTensorCohomologyVanishes X E F i := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  obtain ⟨⟨hpre⟩, _, _⟩ := SheafOfModules.tensorClosed X.sheaf
  let := hpre
  have : E.IsLE b := (DerivedCategory.isLE_iff E b).2 hE
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E b
  obtain ⟨Q, ε, hQ⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    (Opens.grothendieckTopology X) X.sheaf b
  let K' : ObjectProperty.FullSubcategory (fun K : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ↦
        ∀ j : ℤ, b < j → IsZero (K.X j)) :=
    ⟨K, (CochainComplex.isStrictlyLE_iff K b).1 hK⟩
  let P := Q.obj K'
  have hP := hQ K'
  have hflat : CochainComplex.IsKFlatTensor (R := X.sheaf) P :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace X.toRingedSpace P
      ⟨b, hP.2.1⟩ hP.1
  have : QuasiIso (ε.app K') := hP.2.2.2
  have : IsIso (DerivedCategory.Q.map (ε.app K')) := inferInstance
  have hPb : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P b).2 hP.2.1
  refine ⟨P, hflat, ⟨asIso (DerivedCategory.Q.map (ε.app K')) ≪≫ e.symm⟩, ?_⟩
  let L := (HomologicalComplex.single
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ) 0).obj F
  have : CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj P L) (b + 0) :=
    CochainComplex.isStrictlyLE_tensorObj P L b 0
  have : CochainComplex.IsLE (HomologicalComplex.tensorObj P L) b := by simpa using
    (inferInstance : CochainComplex.IsLE (HomologicalComplex.tensorObj P L) (b + 0))
  exact CochainComplex.isZero_of_isLE (HomologicalComplex.tensorObj P L) b i hi

end AlgebraicGeometry
