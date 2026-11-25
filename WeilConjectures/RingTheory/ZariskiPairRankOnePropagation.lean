/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Rank-one propagation for a Zariski pair

A finite flat algebra whose reduction modulo an ideal in the Jacobson radical is the base
quotient has rank one at every prime.

## Implementation details

The rank at a maximal ideal containing the given prime is computed by base change to the
quotient, and rank of a finite flat module is unchanged under specialization.

## References

* Stacks Project, More on Algebra, Lemma 0ELZ
-/

@[expose] public section

universe u v

namespace RingHom

/-- A finite flat algebra whose reduction modulo an ideal in the Jacobson radical is the
base quotient has rank one at every prime: each localization `B_p` is linearly equivalent to
`A_p`. -/
theorem zariskiPair_rank_one_propagation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.FinitePresentation A B]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (hflat : RingHom.Flat (algebraMap A B))
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map)) :
    ∀ (p : Ideal A) [p.IsPrime],
      Nonempty
        (LocalizedModule p.primeCompl B ≃ₗ[Localization.AtPrime p]
          Localization.AtPrime p) := by
  have : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp hflat
  let e := AlgEquiv.ofBijective
    (Algebra.ofId (A ⧸ I) (B ⧸ I.map (algebraMap A B))) hquot
  let e' : TensorProduct A (A ⧸ I) B ≃ₗ[A ⧸ I] A ⧸ I :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv ≪≫ₗ
      e.symm.toLinearEquiv
  intro p hp
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  have : m.IsMaximal := hm
  have hIm : I ≤ m := hI.trans (sInf_le ⟨bot_le, hm⟩)
  obtain ⟨q, hq⟩ : (⟨m, inferInstance⟩ : PrimeSpectrum A) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
    exact hIm
  have : Nontrivial (A ⧸ I) := q.nontrivial
  have hqrank : Module.rankAtStalk (R := A ⧸ I) (TensorProduct A (A ⧸ I) B) q = 1 := by
    rw [Module.rankAtStalk_eq_of_equiv e', Module.rankAtStalk_self]
    rfl
  have hmrank : Module.rankAtStalk (R := A) B ⟨m, inferInstance⟩ = 1 := by
    rw [Module.rankAtStalk_baseChange] at hqrank
    simpa only [Ideal.Quotient.algebraMap_eq, hq] using hqrank
  have hprank : Module.rankAtStalk (R := A) B ⟨p, hp⟩ = 1 :=
    (Module.rankAtStalk_eq_of_le_of_finite_of_flat' B hpm).trans hmrank
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hprank
  exact ⟨e.symm⟩

end RingHom
