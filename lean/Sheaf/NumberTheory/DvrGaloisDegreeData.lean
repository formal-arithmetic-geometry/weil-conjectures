/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank


/-!
# Global degree data for a finite Galois extension of a DVR

Source: literature/stacks-project/more-algebra.tex, Tags 09E8, 09EA and 09EB
(blueprint: lem-exc-dvr-galois-degree-data).
-/

@[expose] public section

universe u v w z

open scoped Pointwise
open Algebra Module

namespace NumberTheory

/-- For a finite normal separable extension of the fraction field of a DVR, the
integral closure has finitely many maximal ideals above the maximal ideal, the
Galois group acts transitively on them, and all local ramification indices and
residue degrees agree; their product with the number of primes is the field
extension degree.  This is the statement of Stacks Tags 09E8, 09EA and 09EB.
(blueprint: lem-exc-dvr-galois-degree-data)

Proof, following Stacks Tags 09E8, 09EA and 09EB and the node's eight steps:

1. A DVR is a PID, hence Noetherian and normal
   (`lem-weil-pbc-pid-noetherian-normal`), and has dimension one
   (`lem-sc-dvr-dimension-one`).
2. Finite separability gives finite normalization
   (`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`). The closure
   is normal with fraction field `L`
   (`lem-weil-pbc-integral-closure-finite-extension-normal`), and is Dedekind with
   surjective spectrum, finite fibres and finite residue extensions
   (`lem-sc-integral-closure-dedekind-surjective-fibres`).
3. Maximal ideals contract to the base maximal ideal by integrality
   (`lem-weil-pbc-integral-algebra-ideal-in-radical`). Conversely primes over it
   are nonzero, hence maximal in this one-dimensional domain. This identifies
   `X` with the finite nonempty fibre.
4. Localizations at these maximal ideals are DVRs
   (`lem-sc-dedekind-localization-dvr`). Their maximal ideals contract to the
   base maximal ideal, so the maps are local. The residue field is `B / q`:
   the map `b/s` to the quotient sends denominators to units, is surjective,
   and has kernel `q B_q`. Thus its degree is finite and positive.
5. The image of any base uniformizer is nonzero and a nonunit. Apply
   `lem-weil-pbc-dvr-unit-times-uniformizer-power` in the local DVR to write it
   as a unit times a power of any local uniformizer. The exponent is positive.
   Cancellation shows uniqueness: two distinct exponents would make a unit
   divisible by a nonunit. Two uniformizers differ by a unit, so changing
   either uniformizer leaves the exponent unchanged. This exponent is the
   length of `B_q / πA B_q`, namely `Ideal.ramificationIdx q A`.
6. The canonical restriction action is transitive on primes with the same
   contraction (`lem-exc-finite-galois-prime-residue-lifting`). It therefore
   acts transitively on `X`.
7. Conjugation gives `A`-algebra isomorphisms between the localizations,
   preserving the base uniformizer. Uniqueness of its exponent identifies
   the ramification indices. The induced residue-field isomorphisms preserve
   residue degrees. Nonemptiness supplies common positive integers `e,f`.
8. Apply `lem-exc-dvr-norm-valuation-sum` to the base uniformizer. Its norm,
   the determinant of scalar multiplication (`def-weil-endomorphism-determinant`),
   is `πA^[L:K]`. The normalized valuation gives `[L:K] = Σ_q e_q f_q`.
   All summands equal `e*f`, giving `[L:K] = |X|*e*f`.
-/
theorem dvr_galois_degree_data
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (B : Type z) [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L] :
    ((IsLocalRing.maximalIdeal A).primesOver B).Finite ∧
      ((IsLocalRing.maximalIdeal A).primesOver B).Nonempty ∧
      (∀ q : Ideal B,
        q.IsMaximal ↔ q ∈ (IsLocalRing.maximalIdeal A).primesOver B) ∧
      MulAction.IsPretransitive (Gal(L / K))
        {q : Ideal B // q ∈ (IsLocalRing.maximalIdeal A).primesOver B} ∧
      (∀ q : {q : Ideal B // q ∈ (IsLocalRing.maximalIdeal A).primesOver B},
        IsDiscreteValuationRing (Localization.AtPrime q.1) ∧
        IsLocalHom (algebraMap A (Localization.AtPrime q.1))) ∧
      (∀ πA : A, Irreducible πA →
        ∀ q : {q : Ideal B // q ∈ (IsLocalRing.maximalIdeal A).primesOver B},
          ∀ tq : Localization.AtPrime q.1, Irreducible tq →
            ∃ e_q f_q : ℕ, 0 < e_q ∧ 0 < f_q ∧
              ∃ u_q : (Localization.AtPrime q.1)ˣ,
                algebraMap A (Localization.AtPrime q.1) πA =
                    (u_q : Localization.AtPrime q.1) * tq ^ e_q ∧
                  e_q = Ideal.ramificationIdx q.1 A ∧
                  f_q = Ideal.inertiaDeg q.1 A) ∧
      (∃ e f g : ℕ,
        0 < e ∧ 0 < f ∧
        g = ((IsLocalRing.maximalIdeal A).primesOver B).ncard ∧
        (∀ q : {q : Ideal B // q ∈ (IsLocalRing.maximalIdeal A).primesOver B},
          Ideal.ramificationIdx q.1 A = e ∧
            Ideal.inertiaDeg q.1 A = f) ∧
        Module.finrank K L = g * e * f) := by
  classical
  let : IsIntegrallyClosed A := inferInstance
  let : Module.Finite A B := IsIntegralClosure.finite A K L B
  let : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  have : IsTorsionFree A L := .trans_faithfulSMul A K L
  let : IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  let : MulSemiringAction (Gal(L / K)) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : IsGaloisGroup (Gal(L / K)) A B :=
    IsGaloisGroup.of_isFractionRing _ _ _ K L
  let p := IsLocalRing.maximalIdeal A
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hmax (q : Ideal B) : q.IsMaximal ↔ q ∈ p.primesOver B := by
    constructor
    · intro hq
      let := hq
      refine ⟨hq.isPrime, ⟨?_⟩⟩
      exact (IsLocalRing.eq_maximalIdeal (inferInstance : (q.under A).IsMaximal)).symm
    · exact Ideal.isMaximal_of_mem_primesOver
  have hlocal (q : p.primesOver B) :
      IsDiscreteValuationRing (Localization.AtPrime q.1) ∧
      IsLocalHom (algebraMap A (Localization.AtPrime q.1)) := by
    have hq0 : q.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp q.2
    refine ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
      hq0 _, ?_⟩
    apply ((IsLocalRing.local_hom_TFAE _).out 4 0).mp
    rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q.1), ← Ideal.comap_comap]
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)).under B).under A = p
    exact congrArg (Ideal.under A)
      (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q.1) q.1) |>.trans
        (Ideal.over_def q.1 p).symm
  refine ⟨IsDedekindDomain.primesOver_finite p B, ?_, hmax, ?_, hlocal, ?_, ?_⟩
  · obtain ⟨q⟩ := (inferInstance : Nonempty (p.primesOver B))
    exact ⟨q.1, q.2⟩
  · change MulAction.IsPretransitive (Gal(L / K)) (p.primesOver B)
    infer_instance
  · intro πA hπ q tq ht
    have := (hlocal q).1
    have := (hlocal q).2
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime q.1)) := by
      rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q.1)]
      exact (IsLocalization.injective (Localization.AtPrime q.1)
        q.1.primeCompl_le_nonZeroDivisors).comp (FaithfulSMul.algebraMap_injective A B)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (by simpa only [map_zero] using hinj.ne hπ.ne_zero) ht
    have hn : 0 < n := by
      apply Nat.pos_of_ne_zero
      intro hn
      have hu' : IsUnit (algebraMap A (Localization.AtPrime q.1) πA) := by
        rw [hu, hn, pow_zero, mul_one]
        exact u.isUnit
      exact hπ.not_isUnit (isUnit_of_map_unit _ _ hu')
    have hideal : p.map (algebraMap A (Localization.AtPrime q.1)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.1) ^ n := by
      calc
        p.map (algebraMap A (Localization.AtPrime q.1)) =
            (Ideal.span {πA}).map (algebraMap A (Localization.AtPrime q.1)) :=
          congrArg (Ideal.map (algebraMap A (Localization.AtPrime q.1))) hπ.maximalIdeal_eq
        _ = Ideal.span {(u : Localization.AtPrime q.1) * tq ^ n} := by
          rw [Ideal.map_span, Set.image_singleton, hu]
        _ = IsLocalRing.maximalIdeal (Localization.AtPrime q.1) ^ n := by
          rw [Ideal.span_singleton_mul_left_unit u.isUnit, ht.maximalIdeal_eq,
            Ideal.span_singleton_pow]
    have he : q.1.ramificationIdx A = n := by
      rw [Ideal.ramificationIdx_eq p q.1, hideal,
        IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
    exact ⟨n, q.1.inertiaDeg A, hn, q.1.inertiaDeg_pos A, u, hu, he.symm, rfl⟩
  · refine ⟨p.ramificationIdxIn B, p.inertiaDegIn B, (p.primesOver B).ncard,
      Nat.pos_of_ne_zero (Ideal.ramificationIdxIn_ne_zero (G := Gal(L / K))),
      Nat.pos_of_ne_zero (Ideal.inertiaDegIn_ne_zero (G := Gal(L / K))), rfl, ?_, ?_⟩
    · intro q
      exact ⟨(Ideal.ramificationIdxIn_eq_ramificationIdx p q.1 (Gal(L / K))).symm,
        (Ideal.inertiaDegIn_eq_inertiaDeg p q.1 (Gal(L / K))).symm⟩
    · rw [mul_assoc,
        Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B (Gal(L / K))]
      exact (IsGalois.card_aut_eq_finrank K L).symm

end NumberTheory
