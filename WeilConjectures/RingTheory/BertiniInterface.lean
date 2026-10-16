/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# TEMPORARY interface statements for the Bertini argument (coordination file, to be deleted)
-/

@[expose] public section

universe u

open scoped Pointwise

/-- (S) generic members of a separating linear system avoid `m²`. -/
theorem Algebra.Smooth.exists_ne_zero_forall_notMem_sq {k A : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Algebra.Smooth k A]
    {M : ℕ} (v : Fin M → A) (S : Set (Ideal A)) (hS : S.Finite)
    (hgen : ∀ m : Ideal A, m.IsMaximal → m ∉ S → ∀ x : A,
      ∃ c : Fin M → k, x - ∑ i, c i • v i ∈ m ^ 2)
    (hSmax : ∀ m ∈ S, m.IsMaximal) (hvS : ∀ m ∈ S, ∀ i, v i ∈ m)
    (hcot : ∀ m ∈ S, ∀ x ∈ m, ∃ c : Fin M → k, x - ∑ i, c i • v i ∈ m ^ 2) :
    ∃ h : MvPolynomial (Fin M) k, h ≠ 0 ∧ ∀ b : Fin M → k, MvPolynomial.eval b h ≠ 0 →
      ∀ m : Ideal A, m.IsMaximal → ∑ i, b i • v i ∈ m → ∑ i, b i • v i ∉ m ^ 2 :=
  sorry

/-- (D) a hypersurface section avoiding `m²` at all its points is smooth, of one less
relative dimension. -/
theorem Algebra.Smooth.quotient_span_singleton {k A : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Algebra.Smooth k A]
    {e : ℕ} (he : Module.rank A Ω[A⁄k] = e + 1) (f : A) (hf0 : f ≠ 0)
    (hf : ∀ m : Ideal A, m.IsMaximal → f ∈ m → f ∉ m ^ 2) :
    Algebra.Smooth k (A ⧸ Ideal.span {f}) ∧ (IsDomain (A ⧸ Ideal.span {f}) →
      Module.rank (A ⧸ Ideal.span {f}) Ω[(A ⧸ Ideal.span {f})⁄k] = e) :=
  sorry

/-- (C) generic members of a linear system with finite base locus `S` cut a finite cover in a
connected scheme. -/
theorem exists_ne_zero_forall_connectedSpace_quotient {k A B : Type u} [Field k]
    [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra k B] [IsScalarTower k A B] (hA : 2 ≤ ringKrullDim A) {M : ℕ} (v : Fin M → A)
    (S : Set (Ideal A)) (hS : S.Finite) (hSmax : ∀ m ∈ S, m.IsMaximal) (hSne : S.Nonempty)
    (hvS : ∀ m ∈ S, ∀ i, v i ∈ m)
    (hbase : ∀ p : Ideal A, p.IsPrime → (∀ i, v i ∈ p) → p ∈ S) :
    ∃ a : MvPolynomial (Fin M) k, a ≠ 0 ∧ ∀ b : Fin M → k, MvPolynomial.eval b a ≠ 0 →
      ConnectedSpace (PrimeSpectrum (B ⧸ Ideal.span {algebraMap A B (∑ i, b i • v i)})) :=
  sorry

/-- (I) ring-level Bertini: a smooth connected curve section through finitely many points,
over which a connected finite étale cover stays connected. -/
theorem Algebra.Smooth.exists_quotient_curve_connectedSpace {k A B : Type u} [Field k]
    [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Algebra.Smooth k A] {d : ℕ} (hd : 2 ≤ d) (hA : Module.rank A Ω[A⁄k] = d)
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B] [Algebra k B]
    [IsScalarTower k A B] [ConnectedSpace (PrimeSpectrum B)]
    (S : Set (Ideal A)) (hS : S.Finite) (hSmax : ∀ m ∈ S, m.IsMaximal) (hSne : S.Nonempty) :
    ∃ J : Ideal A, J.FG ∧ (∀ m ∈ S, J ≤ m) ∧ IsDomain (A ⧸ J) ∧ Algebra.Smooth k (A ⧸ J) ∧
      Module.rank (A ⧸ J) Ω[(A ⧸ J)⁄k] = 1 ∧
      ConnectedSpace (PrimeSpectrum (B ⧸ J.map (algebraMap A B))) :=
  sorry

/-- (E) a smooth algebra over a field with connected spectrum is a domain. -/
theorem Algebra.Smooth.isDomain_of_connectedSpace {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] [ConnectedSpace (PrimeSpectrum A)] : IsDomain A :=
  sorry
