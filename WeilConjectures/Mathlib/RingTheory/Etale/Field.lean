/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Etale.Field

/-!
# Points of étale algebras over a separably closed field

An étale algebra `A` over a separably closed field `K` is a finite product of copies of `K`, so
its `K`-algebra homomorphisms to any field extension `L` of `K` are the projections onto the
factors; in particular there are exactly `dim_K A` of them.

## Main statements

- `Algebra.Etale.finrank_eq_natCard_primeSpectrum`: `dim_K A` is the number of primes of `A`.
- `Algebra.Etale.natCard_algHom_eq_finrank`: `#(A →ₐ[K] L) = dim_K A`.
- `Algebra.Etale.iff_subsingleton_kaehlerDifferential_of_field`: a finite algebra over a field
  is étale if and only if its module of Kähler differentials vanishes.
-/

@[expose] public section

universe u v

open Module

namespace Algebra.Etale

variable (K : Type u) (A : Type u) [Field K] [IsSepClosed K] [CommRing A] [Algebra K A]
  [Algebra.Etale K A]

omit [IsSepClosed K] in
include K in
/-- An étale algebra over a field has finitely many primes. -/
theorem finite_primeSpectrum : Finite (PrimeSpectrum A) := by
  have := Algebra.FormallyUnramified.finite_of_free K A
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  infer_instance

/-- An étale algebra over a separably closed field `K` has `K`-dimension the number of its
primes. -/
theorem finrank_eq_natCard_primeSpectrum : finrank K A = Nat.card (PrimeSpectrum A) := by
  have := finite_primeSpectrum K A
  have := Fintype.ofFinite (PrimeSpectrum A)
  rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed K A).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- The `K`-algebra homomorphism `A →ₐ[K] L` given by the factor of `A ≃ₐ[K] Π_p K` at a
prime `p` of `A`, followed by the inclusion `K → L`. -/
noncomputable def algHomOfPrimeSpectrum (L : Type v) [Field L] [Algebra K L]
    (p : PrimeSpectrum A) : A →ₐ[K] L :=
  (Algebra.ofId K L).comp ((Pi.evalAlgHom K (fun _ ↦ K) p).comp
    (Algebra.FormallyEtale.equivPiOfIsSepClosed K A).toAlgHom)

theorem algHomOfPrimeSpectrum_injective (L : Type v) [Field L] [Algebra K L] :
    Function.Injective (algHomOfPrimeSpectrum K A L) := by
  classical
  intro p q h
  by_contra hpq
  have := congr($h ((Algebra.FormallyEtale.equivPiOfIsSepClosed K A).symm (Pi.single p 1)))
  simp [algHomOfPrimeSpectrum, Ne.symm hpq] at this

/-- An étale algebra `A` over a separably closed field `K` has exactly `dim_K A` algebra
homomorphisms to any field extension `L` of `K`. -/
theorem natCard_algHom_eq_finrank (L : Type v) [Field L] [Algebra K L] :
    Nat.card (A →ₐ[K] L) = finrank K A := by
  have := Algebra.FormallyUnramified.finite_of_free K A
  refine le_antisymm (card_algHom_le_finrank K A L) ?_
  have := finite_primeSpectrum K A
  rw [finrank_eq_natCard_primeSpectrum]
  exact Nat.card_le_card_of_injective _ (algHomOfPrimeSpectrum_injective K A L)

end Algebra.Etale

namespace Algebra.Etale

/-- A finite algebra `A` over a field `K` is étale if and only if `Ω[A⁄K] = 0`.

Part of blueprint `lem-sc-finite-etale-algebra-criterion`. A finite `K`-algebra is of finite
presentation, and over a field formally unramified algebras of finite type are formally
étale. -/
theorem iff_subsingleton_kaehlerDifferential_of_field {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] :
    Algebra.Etale K A ↔ Subsingleton Ω[A⁄K] := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  have : Algebra.FormallyUnramified K A := ⟨h⟩
  exact ⟨.of_formallyUnramified_of_field K A,
    FinitePresentation.of_finiteType.mp inferInstance⟩

end Algebra.Etale
