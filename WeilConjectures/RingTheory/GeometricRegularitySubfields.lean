/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.FieldTheory.IntermediateField.Basic
import WeilConjectures.FieldTheory.FinitePurelyInseparableScalarDescent
import WeilConjectures.FieldTheory.FinitePresentationSubfieldModel

/-!
# Geometric regularity over a directed union of subfields

A Noetherian algebra over a field `k` is geometrically regular if it is geometrically regular
over every member of a directed family of subfields whose union is `k`.

## Implementation details

A finite purely inseparable extension `k'/k` is finitely presented, so it descends to a
finite purely inseparable extension `k_i'` of some subfield `K i`, with
`k ⊗[K i] k_i' ≃ k'`. Then `k' ⊗[k] A ≃ k_i' ⊗[K i] A`, which is regular by hypothesis.
In the identity printed in the Stacks Project, the left side `k_i` is a misprint for `k'`.

## References

* [Stacks, Tag 07QG]
-/

@[expose] public section

universe u v w

/-- A Noetherian algebra that is geometrically regular over each subfield in a directed family
whose union is `k` is geometrically regular over `k`.
-/
theorem geometricallyRegular_of_directed_subfields
    (k : Type u) [Field k]
    (I : Type v) [Nonempty I]
    (K : I → Subfield k)
    (hdir : ∀ i j : I, ∃ l : I, K i ≤ K l ∧ K j ≤ K l)
    (hUnion : ∀ x : k, ∃ i : I, x ∈ K i)
    (A : Type w) [CommRing A] [Algebra k A]
    (hA : IsNoetherianRing A)
    (hgeom : ∀ i : I, Algebra.IsGeometricallyRegular (K i) A) :
    Algebra.IsGeometricallyRegular k A := by
  classical
  refine ⟨hA, ?_⟩
  intro E _ _ _ _
  have : Algebra.FinitePresentation k E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨i, B, hB, aB, ⟨e⟩⟩ := Algebra.exists_subfield_model k I K hdir hUnion E
  let := hB
  let := aB
  have : Module.Finite k (TensorProduct (K i) k B) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have : IsPurelyInseparable k (TensorProduct (K i) k B) :=
    e.symm.isPurelyInseparable
  have ht : IsField (TensorProduct (K i) k B) := by
    exact MulEquiv.isField (Field.toIsField E) e.toMulEquiv
  obtain ⟨hf, hm, hp, _⟩ :=
    Algebra.TensorProduct.finite_purelyInseparable_of_tensorProduct (K i) k B ht
  let : Field B := hf.toField
  have := hm
  have := hp
  have : IsRegularRing (TensorProduct (K i) B A) := (hgeom i).2 B
  let t := (Algebra.TensorProduct.comm (K i) B A).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange (K i) k k A B).toRingEquiv.symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) e).toRingEquiv.trans
        (Algebra.TensorProduct.comm k A E).toRingEquiv))
  exact IsRegularRing.of_ringEquiv t
