/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import WeilConjectures.RingTheory.RegularCompositionExtendedFiber
import WeilConjectures.RingTheory.RegularMapAscent
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Composition of regular ring maps

The composite of regular ring maps is regular when its fibres over the source are Noetherian.

## Implementation details

Fix a prime `p` of `A` and a finite purely inseparable extension `k` of `κ(p)`. Regular base
change makes `B ⊗_A k` Noetherian and regular, and `C ⊗_A k` is Noetherian. The map
`B ⊗_A k → C ⊗_A k` is flat with Noetherian geometrically regular fibres (extensions of the
original fibres along finitely generated residue field extensions). At each prime of
`C ⊗_A k`, a flat local map with regular source and regular closed fibre has regular target
(Tag 031E), so the composite fibre is regular.

## References

* [Stacks, Tag 07QI]
* [Stacks, Tag 031E]
-/

@[expose] public section

universe u v w

namespace RingHom

/-- The composite of regular ring maps is regular when its fibres over the source
are Noetherian. -/
theorem IsRegular.comp_of_fiber_noetherian
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hf : (algebraMap A B).IsRegular) (hg : (algebraMap B C).IsRegular)
    (h : ∀ (p : Ideal A) [p.IsPrime], IsNoetherianRing (p.Fiber C)) :
    (algebraMap A C).IsRegular := by
  rw [IsRegular, toAlgebra_algebraMap] at hf hg ⊢
  refine ⟨?_, ?_⟩
  · simpa only [IsScalarTower.algebraMap_eq A B C] using hf.1.comp hg.1
  · intro p hp
    refine ⟨h p, ?_⟩
    intro K hK hAlg hFin hIns
    have hB : IsRegularRing (TensorProduct p.ResidueField K (p.Fiber B)) :=
      Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular (hf.2 p) K
        (IntermediateField.fg_top _ _)
    have hC : IsNoetherianRing (TensorProduct p.ResidueField K (p.Fiber C)) := by
      have := h p
      let e := Algebra.TensorProduct.comm p.ResidueField K (p.Fiber C)
      have : IsNoetherianRing (TensorProduct p.ResidueField (p.Fiber C) K) :=
        IsNoetherianRing.of_finite (p.Fiber C) _
      exact isNoetherianRing_of_ringEquiv _ e.toRingEquiv.symm
    let f := Algebra.TensorProduct.map (AlgHom.id p.ResidueField K)
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom A B C))
    let := f.toRingHom.toAlgebra
    apply isRegularRing_of_flat_of_regular_fibers
      (R := TensorProduct p.ResidueField K (p.Fiber B))
    · rw [RingHom.algebraMap_toAlgebra]
      exact (hg.1.lTensor (S := p.ResidueField) p.ResidueField).lTensor
        (S := p.ResidueField) K
    · exact IsRegular.extendedFiber_regular (by
        rw [IsRegular, toAlgebra_algebraMap]
        exact hg) p K

end RingHom
