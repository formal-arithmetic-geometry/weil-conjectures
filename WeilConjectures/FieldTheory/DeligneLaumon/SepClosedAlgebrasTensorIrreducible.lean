/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.TensorFiniteTypeLimit
import WeilConjectures.FieldTheory.AlgClosedFiniteTypeTensorDomain

/-!
# Tensor products of irreducible algebras over a separably closed field

Source: Stacks Project, Algebra, Tag 00I7, `lemma-separably-closed-irreducible`
(blueprint: lem-zl-sepclosed-algebras-tensor-irreducible).
The unique-minimal-prime formulation is expressed as irreducibility of the nonempty spectra.
-/

@[expose] public section

universe u v w

open scoped TensorProduct
open AlgebraicGeometry

private theorem quotient_spectrum_homeomorph
    (A : Type*) [CommRing A] (I : Ideal A) (hI : I ≤ nilradical A) :
    Nonempty (PrimeSpectrum A ≃ₜ PrimeSpectrum (A ⧸ I)) := by
  have h := PrimeSpectrum.isHomeomorph_comap (Ideal.Quotient.mk I)
    (fun x ↦ ⟨1, by omega, by simpa using Ideal.Quotient.mk_surjective x⟩)
    (by simpa using hI)
  exact ⟨(h.homeomorph _).symm⟩

private theorem reduced_baseChange_domain
    (k : Type u) [Field k] [IsSepClosed k]
    (A : Type v) [CommRing A] [Algebra k A]
    [IrreducibleSpace (PrimeSpectrum A)] :
    IsDomain ((AlgebraicClosure k ⊗[k] A) ⧸
      nilradical (AlgebraicClosure k ⊗[k] A)) := by
  let Ω := AlgebraicClosure k
  have h := PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k Ω A
  let e := (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm k Ω A).toRingEquiv).trans (h.homeomorph _)
  have : IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] A)) :=
    e.irreducibleSpace_iff.mpr inferInstance
  have : (nilradical (Ω ⊗[k] A)).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  infer_instance

private theorem tensor_reduce_right_homeomorph
    (k A B : Type*) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] :
    Nonempty (PrimeSpectrum (A ⊗[k] B) ≃ₜ
      PrimeSpectrum (A ⊗[k] (B ⧸ nilradical B))) := by
  let I := (nilradical B).map
    (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom
  have hI : I ≤ nilradical (A ⊗[k] B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_nilradical.mpr ((mem_nilradical.mp hx).map _)
  obtain ⟨e⟩ := quotient_spectrum_homeomorph (A ⊗[k] B) I hI
  exact ⟨e.trans (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.tensorQuotientEquiv (R := k) k B A
      (nilradical B)).symm.toRingEquiv)⟩

private theorem tensor_domain_of_algClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (R : Type v) [CommRing R] [IsDomain R] [Algebra k R]
    (S : Type w) [CommRing S] [IsDomain S] [Algebra k S] :
    IsDomain (R ⊗[k] S) := by
  classical
  have : NoZeroDivisors (R ⊗[k] S) := ⟨by
    intro x y hxy
    by_contra! h
    obtain ⟨R', S', hR', hS', x', y', hx', hy', hxy'⟩ :=
      (Algebra.tensor_finite_type_limit k R S).2 ⟨x, y, h.1, h.2, hxy⟩
    have : Algebra.FiniteType k R' := hR'
    have : Algebra.FiniteType k S' := hS'
    have : IsDomain (R' ⊗[k] S') :=
      IsAlgClosed.isDomain_tensorProduct_of_finiteType k R' S'
    exact (eq_zero_or_eq_zero_of_mul_eq_zero hxy').elim hx' hy'⟩
  have : Nontrivial (R ⊗[k] S) := Module.FaithfullyFlat.lTensor_nontrivial k R S
  exact (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨inferInstance, inferInstance⟩

namespace IsSepClosed

end IsSepClosed
