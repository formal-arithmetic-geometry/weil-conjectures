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
The quotient of a localized module by the localized range is the quotient of the
extension of scalars by the extended range.  This is the scalar-extension
transport needed after applying `localizedQuotientEquiv`; it follows by using
`LocalizedModule.equivTensorProduct` on source and target and transporting the
range equality through the induced quotient equivalence.
(blueprint: new-residue-kernel-localized-cokernel-transport)
Source: Mathlib.RingTheory.Localization.BaseChange and
Mathlib.Algebra.Module.LocalizedModule.Submodule.
-/
theorem localized_range_quotient_extendScalars
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    Nonempty ((LocalizedModule 𝔭.primeCompl Y ⧸
        (LinearMap.range f.hom).localized 𝔭.primeCompl) ≃ₗ[Localization.AtPrime 𝔭]
      (((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).obj Y)
        ⧸ LinearMap.range ((ModuleCat.extendScalars
          (algebraMap R (Localization.AtPrime 𝔭))).map f).hom)) := by
  sorry

end ModuleCat
