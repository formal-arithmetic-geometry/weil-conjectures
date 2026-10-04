/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

/-!
# Étale algebras over a normal domain with separably closed fraction field

Let `A` be an integrally closed domain whose fraction field `K` is separably closed, and let `B`
be an étale `A`-algebra. Then every point of `Spec B` lies on a section of `Spec B → Spec A`
defined over a basic open of `Spec A`: for every prime `q` of `B` there are `a : A` and an
`A`-algebra map `ψ : B →ₐ[A] A[1/a]` such that `q` is the pullback along `ψ` of a prime of
`A[1/a]`.

The proof combines Zariski's main theorem with the structure of étale algebras over the
separably closed field `K`. By Zariski's main theorem
(`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`) there is a
module-finite subalgebra `S'` of `B` and `r ∈ S'`, `r ∉ q`, with `S'[1/r] = B[1/r]`. Since `B`
is flat over `A`, it embeds into `K ⊗[A] B`, which is a finite product of copies of `K`; so the
`A`-algebra maps `φ : B →ₐ[A] K` are jointly injective, and as `q` is prime and there are
finitely many of them, `q` contains the kernel of one of them. This `φ` maps the integral
`A`-algebra `S'` into the integral closure `A` of `A` in `K`, hence `B` into `A[1/φ(r)]`.

Specialising to a local ring gives that an integrally closed local domain with separably
closed fraction field is strictly henselian.

## Main results

- `Algebra.Etale.exists_algHom_localizationAway_comap_eq`: the section statement above.
- `Algebra.Etale.exists_algHom_comap_maximalIdeal_eq`: over an integrally closed local domain
  with separably closed fraction field, every prime of an étale algebra over the closed point
  is the pullback of the maximal ideal along an `A`-algebra map `B →ₐ[A] A`.
- `HenselianLocalRing.of_isSepClosed_fractionRing`,
  `IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing`: such a local ring is
  henselian with separably closed residue field, i.e. it is strictly henselian.
-/

@[expose] public section

open Polynomial

namespace Algebra.Etale

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
  [Algebra A B] [Algebra.Etale A B]

/-- **Points of an étale algebra over a normal domain with separably closed fraction field lie
on sections.** Let `A` be an integrally closed domain with separably closed fraction field `K`
and `B` an étale `A`-algebra. Then for every prime `q` of `B` there are `a : A` and an
`A`-algebra map `ψ : B →ₐ[A] A[1/a]` such that `q` is the preimage of a prime of `A[1/a]`
under `ψ`. This is the algebraic heart of Stacks Project, Lemma 59.80.4 (Tag 09Z9). -/
theorem exists_algHom_localizationAway_comap_eq (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsSepClosed K] (q : Ideal B) [q.IsPrime] :
    ∃ (a : A) (ψ : B →ₐ[A] Localization.Away a) (P : Ideal (Localization.Away a)),
      P.IsPrime ∧ P.comap ψ = q :=
  sorry

/-- Over an integrally closed local domain `A` with separably closed fraction field, every prime
`q` of an étale `A`-algebra `B` lying over the maximal ideal is the preimage of the maximal ideal
under an `A`-algebra map `B →ₐ[A] A`. -/
theorem exists_algHom_comap_maximalIdeal_eq [IsLocalRing A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsSepClosed K] (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    ∃ ψ : B →ₐ[A] A, (IsLocalRing.maximalIdeal A).comap ψ = q :=
  sorry

end Algebra.Etale

variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]

/-- An integrally closed local domain with separably closed fraction field is henselian. -/
theorem HenselianLocalRing.of_isSepClosed_fractionRing (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsSepClosed K] : HenselianLocalRing A :=
  sorry

/-- An integrally closed local domain with separably closed fraction field has separably closed
residue field. -/
theorem IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing (K : Type*) [Field K]
    [Algebra A K] [IsFractionRing A K] [IsSepClosed K] :
    IsSepClosed (IsLocalRing.ResidueField A) :=
  sorry
