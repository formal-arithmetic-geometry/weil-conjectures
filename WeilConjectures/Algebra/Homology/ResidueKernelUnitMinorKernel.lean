/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import WeilConjectures.Algebra.Homology.ResidueKernelUnitMinorMatrixCore
import WeilConjectures.Algebra.Homology.ResidueKernelUnitMinorBaseChangeFree
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Normal form of the residue unit-minor matrix

## References

* Stacks Project, Tags 00O0 and 00NX (unit-minor argument)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat
/-- The matrix part of the residue unit-minor argument, before computing kernels or cokernels. -/
theorem residue_kernel_unit_minor_normal_form
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (hfX : Module.Finite R X) (hfY : Module.Finite R Y)
    (hpX : Module.Projective R X) (hpY : Module.Projective R Y)
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars
      ((IsLocalRing.residue (Localization.AtPrime 𝔭)).comp
        (algebraMap R (Localization.AtPrime 𝔭)))).map f).hom
      ≃ₗ[IsLocalRing.ResidueField (Localization.AtPrime 𝔭)]
        IsLocalRing.ResidueField (Localization.AtPrime 𝔭))) :
    ∃ (U C : ModuleCat.{v} (Localization.AtPrime 𝔭))
      (g : Localization.AtPrime 𝔭 →ₗ[Localization.AtPrime 𝔭] C),
      Module.Free (Localization.AtPrime 𝔭) C ∧
      ∃ (eX : ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj X)
          ≃ₗ[Localization.AtPrime 𝔭] (U × Localization.AtPrime 𝔭))
        (eY : ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y)
          ≃ₗ[Localization.AtPrime 𝔭] (U × C)),
        ∀ x, eY (((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).map f).hom
          x) = ((eX x).1, g (eX x).2) := by
  let A := Localization.AtPrime 𝔭
  have hfree := residue_kernel_unit_minor_base_change_free R X Y hfX hfY hpX hpY 𝔭
  let := hfX
  let := hfY
  exact residue_kernel_unit_minor_matrix_core R A X Y f hfree.1 hfree.2
    (by
      dsimp [extendScalars, ExtendScalars.obj', restrictScalars, RestrictScalars.obj']
      let : Algebra R A := (algebraMap R A).toAlgebra
      infer_instance)
    (by
      dsimp [extendScalars, ExtendScalars.obj', restrictScalars, RestrictScalars.obj']
      let : Algebra R A := (algebraMap R A).toAlgebra
      infer_instance) 𝔭 hres
end ModuleCat
