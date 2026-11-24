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
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import WeilConjectures.Algebra.Homology.ResidueKernelUnitMinorKernel
import WeilConjectures.Algebra.Homology.ResidueKernelUnitMinorQuotient
import WeilConjectures.Algebra.Homology.ResidueKernelLocalizedCokernel

/-! # Unit-minor reduction for a residue rank-one kernel

## References

* Stacks Project, Tag 00O0 (local matrix argument)
* Stacks Project, Tag 00NX
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

/-- The unit-minor step reduces the localized cokernel to the cokernel of a
map with rank-one source, retaining the entire localized kernel. -/
theorem residue_kernel_unit_minor
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (hfX : Module.Finite R X) (hfY : Module.Finite R Y)
    (hpX : Module.Projective R X) (hpY : Module.Projective R Y)
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars
      ((IsLocalRing.residue (Localization.AtPrime 𝔭)).comp
        (algebraMap R (Localization.AtPrime 𝔭)))).map f).hom
      ≃ₗ[IsLocalRing.ResidueField (Localization.AtPrime 𝔭)]
        IsLocalRing.ResidueField (Localization.AtPrime 𝔭))) :
    ∃ (C : ModuleCat.{v} (Localization.AtPrime 𝔭))
      (g : Localization.AtPrime 𝔭 →ₗ[Localization.AtPrime 𝔭] C),
      Module.Free (Localization.AtPrime 𝔭) C ∧
      Nonempty (LinearMap.ker g ≃ₗ[Localization.AtPrime 𝔭]
        LinearMap.ker ((ModuleCat.extendScalars
          (algebraMap R (Localization.AtPrime 𝔭))).map f).hom) ∧
      Nonempty (LocalizedModule 𝔭.primeCompl (Y ⧸ LinearMap.range f.hom)
        ≃ₗ[Localization.AtPrime 𝔭] (C ⧸ LinearMap.range g)) := by
  obtain ⟨U, C, g, hfree, eX, eY, hdiag⟩ :=
    residue_kernel_unit_minor_normal_form R X Y f hfX hfY hpX hpY 𝔭 hres
  obtain ⟨hker, hcoker⟩ := residue_kernel_unit_minor_quotient
    (Localization.AtPrime 𝔭) _ _ U C
    ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).map f).hom
    g eX eY hdiag
  obtain ⟨eLoc⟩ := residue_kernel_localized_cokernel R X Y f 𝔭
  obtain ⟨eCoker⟩ := hcoker
  exact ⟨C, g, hfree, hker, ⟨eLoc.trans eCoker⟩⟩

end ModuleCat
