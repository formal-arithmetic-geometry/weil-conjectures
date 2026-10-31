/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.FieldTheory.MakeSeparablyGenerated
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced

/-!
# Finite purely inseparable test for geometric reducedness

Source: Stacks Project, Algebra, Tag 030V, lemma-geometrically-reduced-finite-
purely-inseparable-extension, equivalence of (1) and (5)
(blueprint: lem-trf-geometric-reducedness-finite-inseparable-test).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- For an arbitrary commutative algebra over a field, reducedness after finite purely
inseparable field extensions is equivalent to reducedness after all field extensions.
Source: Stacks Project, Algebra, Tag 030V, lemma-geometrically-reduced-finite-
purely-inseparable-extension, equivalence of (1) and (5)
(blueprint: lem-trf-geometric-reducedness-finite-inseparable-test).

The proof follows Tag 030V.  Restriction to finite purely inseparable extensions is
immediate.  For the converse, a finitely generated field extension is placed in the
finite purely inseparable and separably generated square of
`lem-weil-pbc-make-separably-generated`; reducedness is preserved across its
separably generated upper edge by `lem-weil-pbc-separably-generated-tensor-reduced`,
and tensor cancellation identifies the resulting tensor product.  Flatness of a
module over a field descends reducedness along the finite extension.  Finally, any
nilpotent in a tensor product with an arbitrary field extension uses only finitely
many coefficients, so it descends to a finitely generated intermediate field and
the preceding argument applies.  The tensor products use their usual ring
multiplication and `IsReduced` means that every nilpotent element is zero.
-/
theorem isReduced_tensorProduct_iff_forall_finitePurelyInseparable
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C] :
    (∀ (E : Type (max u v)) [Field E] [Algebra k E]
      [Module.Finite k E] [IsPurelyInseparable k E],
      IsReduced (C ⊗[k] E)) ↔
      (∀ (K : Type (max u v)) [Field K] [Algebra k K],
        IsReduced (C ⊗[k] K)) := by
  classical
  constructor
  · intro h K _ _
    have hfg (F : Type (max u v)) [Field F] [Algebra k F]
        (hF : (⊤ : IntermediateField k F).FG) : IsReduced (C ⊗[k] F) := by
      obtain ⟨E, hE, akE, L, hL, aFL, aEL, hfinE, hpureE, _, _,
          hsep, hsquare⟩ :=
        FieldExtension.exists_finitePurelyInseparable_separablyGenerated k F hF
      let : Field E := hE
      let : Algebra k E := akE
      let : Field L := hL
      let : Algebra F L := aFL
      let : Algebra E L := aEL
      have : Module.Finite k E := hfinE
      have : IsPurelyInseparable k E := hpureE
      let : Algebra k L := ((algebraMap F L).comp (algebraMap k F)).toAlgebra
      have : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq' rfl
      have : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq' hsquare.symm
      have : IsReduced (C ⊗[k] E) := h E
      have : IsReduced (E ⊗[k] C) :=
        isReduced_of_injective (Algebra.TensorProduct.comm k E C) (AlgEquiv.injective _)
      have : IsReduced (L ⊗[E] (E ⊗[k] C)) :=
        isReduced_tensorProduct_of_isSeparablyGenerated E L (E ⊗[k] C) hsep
      have : IsReduced (L ⊗[k] C) :=
        isReduced_of_injective
          (Algebra.TensorProduct.cancelBaseChange k E L L C).symm (AlgEquiv.injective _)
      have : IsReduced (F ⊗[k] C) := by
        let f := IsScalarTower.toAlgHom k F L
        exact isReduced_of_injective
          (Algebra.TensorProduct.map f (AlgHom.id k C))
          (Module.Flat.rTensor_preserves_injective_linearMap (M := C) f.toLinearMap
            (algebraMap F L).injective)
      exact isReduced_of_injective (Algebra.TensorProduct.comm k C F) (AlgEquiv.injective _)
    refine ⟨fun z hz ↦ ?_⟩
    obtain ⟨s, hs⟩ := TensorProduct.exists_finset z
    let F := IntermediateField.adjoin k ((s.image Prod.snd : Finset K) : Set K)
    have : Algebra.EssFiniteType k F :=
      IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_finset _)
    have : IsReduced (C ⊗[k] F) := hfg F (IntermediateField.fg_top k F)
    let j := Algebra.TensorProduct.map (AlgHom.id k C) F.val
    have hj : Function.Injective j :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := C) F.val.toLinearMap
        Subtype.val_injective
    have hmem (x : C × K) (hx : x ∈ s) : x.2 ∈ F :=
      IntermediateField.subset_adjoin k _
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
    let zF : C ⊗[k] F := ∑ x ∈ s.attach, x.1.1 ⊗ₜ ⟨x.1.2, hmem _ x.2⟩
    have hzF : j zF = z := by
      rw [hs]
      simp only [zF, map_sum, j, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact Finset.sum_attach s fun x ↦ x.1 ⊗ₜ x.2
    have hzFnil : IsNilpotent zF :=
      (IsNilpotent.map_iff hj).mp (hzF.symm ▸ hz)
    rw [← hzF, IsReduced.eq_zero zF hzFnil, map_zero]
  · intro h E _ _ _ _
    exact h E

end Algebra
