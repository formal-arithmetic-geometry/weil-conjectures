/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
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

/-- If two commutative algebras over a separably closed field have irreducible spectra,
then their tensor product has irreducible spectrum. The canonical tensor algebra has
`(a ⊗ b) * (a' ⊗ b') = (a * a') ⊗ (b * b')` and unit `1 ⊗ 1`.
Source: Stacks Project, Algebra, Tag 00I7, `lemma-separably-closed-irreducible`
(blueprint: lem-zl-sepclosed-algebras-tensor-irreducible).

Proof:
1. Choose an algebraic closure Ω of k (def-weil-algebraic-closure). Since k is separably
closed, Ω/k is purely inseparable (lem-pc-kbar-pure-insep), also in characteristic zero.
Set AΩ = A ⊗[k] Ω, BΩ = B ⊗[k] Ω and T = (A ⊗[k] B) ⊗[k] Ω.
2. Apply lem-pc-homeo-pure-insep to Spec C for C = A, B and A ⊗[k] B. Identify the
base changes using lem-weil-pbc-fibre-product-affine-spectra. The spectra of AΩ and BΩ
are irreducible, and Spec T is homeomorphic to Spec (A ⊗[k] B). Homeomorphisms preserve
both nonemptiness and the intersection property for nonempty opens.
3. Identify V = AΩ ⊗[Ω] BΩ with T by sending (a ⊗ λ) ⊗ (b ⊗ μ) to (a ⊗ b) ⊗ λμ.
The inverse sends (a ⊗ b) ⊗ ν to (a ⊗ ν) ⊗ (b ⊗ 1). Both formulas are balanced and
multiplicative, so def-weil-pbc-module-tensor-product and
lem-weil-pbc-algebra-tensor-pushout-universal-property give ring maps. Their composites
fix pure tensors, moving μ between factors by Ω-balancing, hence are identities.
4. By lem-zl-spectrum-irreducible-nilradical-prime the nilradicals of AΩ and BΩ are
proper prime ideals. Thus their quotients R and S are nonzero domains and Ω-algebras:
a zero product in a quotient lifts to a product in its prime nilradical, and properness
ensures that 1 is not zero.
5. Put U = R ⊗[Ω] S. The quotient maps induce a surjective ring map q : V → U by
lem-weil-pbc-algebra-tensor-pushout-universal-property: pure tensors lift and generate.
Let J be generated by a ⊗ 1 for nilpotent a in AΩ and 1 ⊗ b for nilpotent b in BΩ.
These generators vanish under q. Conversely, sending ā ⊗ b̄ to (a ⊗ b) modulo J is
independent of representatives. The tensor universal property gives U → V/J, inverse
on pure tensors to the induced V/J → U, so ker q = J.
6. Each generator g of J is nilpotent by the multiplication rule. An element of J is a
finite sum ∑ tᵢ gᵢ. Choose positive eᵢ with gᵢ^eᵢ = 0. Every monomial in the power
1 + ∑ (eᵢ - 1) of this sum has at least eᵢ occurrences of some gᵢ, so vanishes. The
empty sum is zero. Thus every element of ker q is nilpotent, without a uniform exponent.
7. By lem-pur-field-vector-space-tensor-nontrivial, U is nonzero. If it had a nonzero
zero-divisor, clause (2) of lem-weil-pbc-tensor-finite-type-limit would give finitely
generated Ω-subalgebras R' and S' whose tensor product has a nonzero zero-divisor.
As unital subrings of R and S these are nonzero domains. The theorem
lem-weil-pbc-algclosed-finite-type-tensor-domain says R' ⊗[Ω] S' is a domain,
a contradiction. Therefore U is a domain, without finite-generation assumptions on R,S.
8. A nilpotent in V maps to zero in the domain U, while Step 6 gives the converse.
Hence the nilradical of V equals ker q, which is proper since U is nonzero and prime
since U has no zero-divisors. By lem-zl-spectrum-irreducible-nilradical-prime, Spec V
is irreducible, including nonempty. Transport across the ring isomorphism in Step 3
and the homeomorphism in Step 2 to obtain the conclusion. -/
theorem irreducibleSpace_tensorProduct
    (k : Type u) [Field k] [IsSepClosed k]
    (A : Type v) [CommRing A] [Algebra k A]
    (B : Type w) [CommRing B] [Algebra k B]
    [IrreducibleSpace (Spec (CommRingCat.of A))]
    [IrreducibleSpace (Spec (CommRingCat.of B))] :
    IrreducibleSpace (Spec (CommRingCat.of (A ⊗[k] B))) := by
  let Ω := AlgebraicClosure k
  let AΩ := Ω ⊗[k] A
  let BΩ := Ω ⊗[k] B
  let R := AΩ ⧸ nilradical AΩ
  let S := BΩ ⧸ nilradical BΩ
  have : IrreducibleSpace (PrimeSpectrum A) :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of A)))
  have : IrreducibleSpace (PrimeSpectrum B) :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of B)))
  have : IsDomain R := reduced_baseChange_domain k A
  have : IsDomain S := reduced_baseChange_domain k B
  have : IsDomain (R ⊗[Ω] S) := tensor_domain_of_algClosed Ω R S
  have h := PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k Ω (A ⊗[k] B)
  let e₀ := (h.homeomorph _).symm.trans
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k (A ⊗[k] B) Ω).toRingEquiv)
  let f : (AΩ ⊗[Ω] BΩ) ≃ₐ[Ω] Ω ⊗[k] (A ⊗[k] B) :=
    (Algebra.TensorProduct.cancelBaseChange k Ω Ω AΩ B).trans
      (Algebra.TensorProduct.assoc k k Ω Ω A B)
  let e₁ := PrimeSpectrum.homeomorphOfRingEquiv f.symm.toRingEquiv
  obtain ⟨e₂⟩ := tensor_reduce_right_homeomorph Ω AΩ BΩ
  let e₃ := PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm Ω AΩ S).toRingEquiv
  obtain ⟨e₄⟩ := tensor_reduce_right_homeomorph Ω S AΩ
  let e₅ := PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm Ω S R).toRingEquiv
  let e := e₀.trans (e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅))))
  exact e.irreducibleSpace_iff.mpr inferInstance

end IsSepClosed
