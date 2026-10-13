module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

/--
There is an A-linear equivalence from the localization of Y to its scalar extension
that carries the localized range of f to the range of the scalar-extended map.
Use `LocalizedModule.equivTensorProduct` and
`LinearMap.localized'_range_eq_range_localizedMap`, then compare the tensor
product object with `ModuleCat.extendScalars`.
(blueprint: new-residue-kernel-localized-cokernel-transport-aux)
Source: Mathlib.RingTheory.Localization.BaseChange and
Mathlib.Algebra.Module.LocalizedModule.Submodule.
-/
theorem localized_range_quotient_extendScalars_aux
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ e : LocalizedModule 𝔭.primeCompl (Y : Type v) ≃ₗ[Localization.AtPrime 𝔭]
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y : Type v),
      ((LinearMap.range f.hom).localized 𝔭.primeCompl).map e.toLinearMap =
        LinearMap.range ((ModuleCat.extendScalars
          (algebraMap R (Localization.AtPrime 𝔭))).map f).hom := by
  sorry

/--
The quotient of a localized module by the localized range is the quotient of the
extension of scalars by the extended range, obtained by transporting the range
identification through `Submodule.Quotient.equiv`.
(blueprint: new-residue-kernel-localized-cokernel-transport)
-/
theorem localized_range_quotient_extendScalars
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    Nonempty ((LocalizedModule 𝔭.primeCompl Y ⧸
        (LinearMap.range f.hom).localized 𝔭.primeCompl) ≃ₗ[Localization.AtPrime 𝔭]
      (((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y)
        ⧸ LinearMap.range ((ModuleCat.extendScalars
          (algebraMap R (Localization.AtPrime 𝔭))).map f).hom)) := by
  obtain ⟨e, he⟩ := localized_range_quotient_extendScalars_aux R X Y f 𝔭
  exact ⟨Submodule.Quotient.equiv _ _ e he⟩

end ModuleCat
