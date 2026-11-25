/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Tensoring a reduced algebra with a separably generated field extension

If `K/k` is a separably generated field extension and `S` is a reduced `k`-algebra, then
`K ⊗[k] S` is reduced.

## Implementation details

Put `E = k(s)` for a separating transcendence basis `s`. Reducedness of `S ⊗[k] E` is checked
on residue fields of `S`, where `E ⊗[k] -` is a localization of a polynomial ring. A separable
algebraic extension preserves reducedness (reduce to residue fields and to finitely generated
subalgebras, which are formally unramified); apply this to `K/E` and `E ⊗[k] S`, and identify
`K ⊗[E] (E ⊗[k] S)` with `K ⊗[k] S`.

## References

* Stacks Project, Algebra, Lemma 10.43.6 (Tag 030U), separably generated case.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

-- The algebraic case of Stacks Tag 030U, using finite subalgebras and residue fields.
private theorem isReduced_tensorProduct_of_separable_algebraic
    (k : Type u) (K : Type v) (S : Type w)
    [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S]
    [Algebra.IsSeparable k K] [IsReduced S] : IsReduced (K ⊗[k] S) := by
  have : IsReduced (S ⊗[k] K) := by
    refine isReduced_tensorProduct_of_forall_residueField fun p ↦ ?_
    refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
    let : Field B := (B.isField_of_algebraic).toField
    have : Algebra.IsSeparable k B := Algebra.IsSeparable.of_algHom k K B.val
    have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
    have : Algebra.FormallyUnramified k B := Algebra.FormallyUnramified.of_isSeparable k B
    exact Algebra.FormallyUnramified.isReduced_of_field p.asIdeal.ResidueField _
  exact isReduced_of_injective (Algebra.TensorProduct.comm k K S) (AlgEquiv.injective _)

/-- Tensoring a reduced commutative `k`-algebra with a separably generated field extension
of `k` gives a reduced ring. -/
theorem isReduced_tensorProduct_of_isSeparablyGenerated
    (k : Type u) (K : Type v) (S : Type w)
    [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S] [IsReduced S]
    (hK : IsSeparablyGenerated k K) : IsReduced (K ⊗[k] S) := by
  obtain ⟨s, hs, hsep⟩ := hK
  let E := IntermediateField.adjoin k s
  have : Algebra.IsSeparable E K := hsep
  have hE : IsReduced (S ⊗[k] E) := by
    refine isReduced_tensorProduct_of_forall_residueField fun p ↦ ?_
    have h := isReduced_tensorProduct_adjoin_of_algebraicIndependent
      (K := p.asIdeal.ResidueField) hs.1
    rw [Subtype.range_coe_subtype] at h
    exact h
  have : IsReduced (E ⊗[k] S) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k E S) (AlgEquiv.injective _)
  have : IsReduced (K ⊗[E] (E ⊗[k] S)) :=
    isReduced_tensorProduct_of_separable_algebraic E K (E ⊗[k] S)
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange k E K K S).symm (AlgEquiv.injective _)

end Algebra

