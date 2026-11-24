/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.Algebra.Homology.ResidueKernelLocalizedCokernelTransport

/-! # Localization of a cokernel versus scalar extension

## References

* `Mathlib.Algebra.Module.LocalizedModule.Submodule`
* `Mathlib.RingTheory.Localization.BaseChange`
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

/-- Localizing a cokernel agrees with the cokernel of scalar extension. -/
theorem residue_kernel_localized_cokernel
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    Nonempty (LocalizedModule 𝔭.primeCompl (Y ⧸ LinearMap.range f.hom)
      ≃ₗ[Localization.AtPrime 𝔭]
        (((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y)
          ⧸ LinearMap.range ((ModuleCat.extendScalars
            (algebraMap R (Localization.AtPrime 𝔭))).map f).hom)) := by
  obtain ⟨e⟩ := localized_range_quotient_extendScalars R X Y f 𝔭
  exact ⟨(localizedQuotientEquiv 𝔭.primeCompl (LinearMap.range f.hom)).symm.trans e⟩

end ModuleCat
