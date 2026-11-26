/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.GeometricallyRegularDescent

/-!
# Permanence of regular ring maps

If `A → C` is regular and `B → C` is flat with surjective map on spectra, then `A → B` is
regular.

## Implementation details

`B → C` is faithfully flat, so flatness of `A → B` descends
(`Module.Flat.of_flat_of_faithfullyFlat`). Each fibre `p.Fiber C ≅ (p.Fiber B) ⊗[B] C` is a
faithfully flat extension of `p.Fiber B`, and geometric regularity descends by
`Algebra.isGeometricallyRegular_of_faithfullyFlat`.

## References

* [Stacks, Tag 07NT]
* [Stacks, Tags 039V, 07NH]
-/

@[expose] public section

universe u v w

namespace RingHom

/-- Regularity descends along a flat map inducing a surjection on spectra. -/
theorem isRegular_of_isRegular_comp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hcomp : (algebraMap A C).IsRegular)
    (hflat : (algebraMap B C).Flat)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B C))) :
    (algebraMap A B).IsRegular := by
  have hBC : Module.FaithfullyFlat B C :=
    (faithfullyFlat_algebraMap_iff).mp
      (FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hflat, hsurj⟩)
  rw [IsRegular, toAlgebra_algebraMap] at hcomp ⊢
  refine ⟨?_, ?_⟩
  · have : Module.Flat A C := flat_algebraMap_iff.mp hcomp.1
    exact flat_algebraMap_iff.mpr (Module.Flat.of_flat_of_faithfullyFlat (C := C))
  · intro p hp
    let f : p.Fiber B →ₐ[p.ResidueField] p.Fiber C :=
      Algebra.TensorProduct.lTensor p.ResidueField (IsScalarTower.toAlgHom A B C)
    let : Algebra (p.Fiber B) (p.Fiber C) := f.toRingHom.toAlgebra
    have : IsScalarTower p.ResidueField (p.Fiber B) (p.Fiber C) :=
      IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    have : Module.FaithfullyFlat (p.Fiber B) (p.Fiber C) := by
      let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
      let e : p.Fiber C ≃ₐ[p.Fiber B] TensorProduct B (p.Fiber B) C :=
        { __ := (Algebra.IsPushout.cancelBaseChangeAlg A p.ResidueField B (p.Fiber B) C).symm,
          commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor
            A B C p.ResidueField) x) }
      exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv
    exact Algebra.isGeometricallyRegular_of_faithfullyFlat
      p.ResidueField (p.Fiber B) (p.Fiber C) (hcomp.2 p)

end RingHom
