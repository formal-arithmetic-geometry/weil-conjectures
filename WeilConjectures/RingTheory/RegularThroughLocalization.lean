/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.GeometricRegularityFieldIso

/-!
# Regularity through localization

If a ring map out of a localization `A'` of `A` is regular after precomposition with the
localization map, then it is regular.

## Implementation details

Flatness over `A'` follows from flatness over `A`. For a prime `q'` of `A'` with inverse image
`q`, the residue fields agree and `C ⊗[A] κ(q) → C ⊗[A'] κ(q')` is a ring isomorphism compatible
with the residue field scalars, so the fibres, and their base changes along finite purely
inseparable extensions, are identified.

## References

* [Stacks, Tag 07PT] (proof)
* [Stacks, Tags 00HT, 00E3, 00C9, 00DL, 0382, 07BZ]
-/

@[expose] public section

universe u v w

namespace RingHom

/-- If a ring map out of a localization is regular after precomposition with the
localization map, then the map out of the localization is regular. Here ψ is
`algebraMap A' C` and the composite ψ ∘ λ is `algebraMap A C` through
`IsScalarTower A A' C`. -/
theorem isRegular_of_comp_algebraMap_localization
    {A : Type u} {A' : Type v} {C : Type w}
    [CommRing A] [CommRing A'] [CommRing C]
    [Algebra A A'] [Algebra A' C] [Algebra A C] [IsScalarTower A A' C]
    (W : Submonoid A) [IsLocalization W A']
    (hψ : (algebraMap A C).IsRegular) :
    (algebraMap A' C).IsRegular := by
  rw [RingHom.IsRegular, toAlgebra_algebraMap] at hψ ⊢
  refine ⟨?_, ?_⟩
  · rw [RingHom.flat_algebraMap_iff]
    have hflat : Module.Flat A C := (RingHom.flat_algebraMap_iff).mp hψ.1
    exact (Module.flat_iff_of_isLocalization A' W C).mpr hflat
  · intro q' hq'
    let q := q'.comap (algebraMap A A')
    have : q.IsPrime := Ideal.IsPrime.comap (algebraMap A A')
    let σ : q.ResidueField ≃ₐ[A] q'.ResidueField :=
      AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ q q' (Algebra.ofId A A') rfl)
        ((RingHom.surjectiveOnStalks_of_isLocalization W A').residueFieldMap_bijective
          q q' rfl)
    let e₁ := Algebra.TensorProduct.congr σ (AlgEquiv.refl : C ≃ₐ[A] C)
    have : TensorProduct.CompatibleSMul A A' q'.ResidueField C :=
      IsLocalization.tensorProduct_compatibleSMul W A' q'.ResidueField C
    let e₂ := Algebra.TensorProduct.equivOfCompatibleSMul A A' q'.ResidueField
      q'.ResidueField C
    exact Algebra.isGeometricallyRegular_of_fieldIso σ.toRingEquiv
      (e₁.toRingEquiv.trans e₂.symm.toRingEquiv) (by
        intro x y
        induction y using TensorProduct.inductionOn with
        | tmul a c =>
          change e₂.symm (σ (x * a) ⊗ₜ[A] c) =
            σ x • e₂.symm (σ a ⊗ₜ[A] c)
          simp [e₂, Algebra.TensorProduct.equivOfCompatibleSMul,
            Algebra.TensorProduct.mapOfCompatibleSMul,
            Algebra.smul_def]
        | add a b ha hb => simp_all) (hψ.2 q)

end RingHom
