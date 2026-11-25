/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Localization.Integer
import WeilConjectures.RingTheory.PopescuDenominatorBasisEnlargement

/-!
# Enlargement before lifting generators

We enlarge an admissible subalgebra `A₀` of the Artinian quotient `Λ_q / q^n Λ_q` to an
admissible `A` such that suitable elements of `Λ` map into `A` with residue differentials forming
a basis, and elements of `q` give generators of the maximal ideal of the quotient.

## Implementation details

The statement only concerns the quotient: it does not assert generation of the localized prime
ideal, the contraction identification of `m_A`, or the compatibility of residue embeddings. The
enlargement distinguishes whether the residue of the common denominator is transcendental or
algebraic over the residue field of `A₀`. Finiteness of `Ω[F₀/k]` follows from essential finite
type, without the Cartier equality.

## References

* [Stacks, Tag 07FH] and [Stacks, Tag 07FI] (proofs)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

private theorem exists_residue_differential_basis
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [EssFiniteType k A] :
    ∃ (t : ℕ) (a : Fin t → A)
      (b : Module.Basis (Fin t) (IsLocalRing.ResidueField A)
        (KaehlerDifferential k (IsLocalRing.ResidueField A))),
      ∀ j, b j = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
        (IsLocalRing.residue A (a j)) := by
  classical
  let F := IsLocalRing.ResidueField A
  let : EssFiniteType k F :=
    EssFiniteType.of_surjective (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal A))
      Ideal.Quotient.mk_surjective
  let b := Module.Basis.ofSpan
    (le_of_eq (KaehlerDifferential.span_range_derivation k F).symm)
  have finish {ι : Type v} (b : Module.Basis ι F (KaehlerDifferential k F))
      (hb : Set.range b ⊆ Set.range (KaehlerDifferential.D k F)) :
      ∃ (t : ℕ) (a : Fin t → A)
        (b : Module.Basis (Fin t) F (KaehlerDifferential k F)),
        ∀ j, b j = KaehlerDifferential.D k F (IsLocalRing.residue A (a j)) := by
    have : Finite ι := b.linearIndependent.finite
    let : Fintype ι := Fintype.ofFinite _
    let e := Fintype.equivFin ι
    let b' := b.reindex e
    have hb' : ∀ j, ∃ a : A, b' j = KaehlerDifferential.D k F (IsLocalRing.residue A a) := by
      intro j
      obtain ⟨c, hc⟩ := hb (Set.mem_range_self (e.symm j))
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) c
      exact ⟨a, by simpa [b', Module.Basis.reindex_apply] using hc.symm⟩
    choose a ha using hb'
    exact ⟨Fintype.card ι, a, b', ha⟩
  exact finish b (Module.Basis.ofSpan_subset _)


private theorem common_denominator
    {Λ : Type v} [CommRing Λ] (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) {ι : Type*} [Finite ι]
    (z : ι → Localization.AtPrime q ⧸ (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) :
    ∃ (s : Λ) (_ : s ∉ q) (μ : ι → Λ), ∀ i,
      Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
        (algebraMap Λ (Localization.AtPrime q) (μ i)) =
      z i * Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
        (algebraMap Λ (Localization.AtPrime q) s) := by
  classical
  let L := Localization.AtPrime q
  let J := q.map (algebraMap Λ L)
  choose l hl using fun i ↦ Ideal.Quotient.mk_surjective (I := J ^ n) (z i)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite q.primeCompl l
  choose μ hμ using hs
  refine ⟨s, s.property, μ, fun i ↦ ?_⟩
  have he := congrArg (Ideal.Quotient.mk (J ^ n)) (hμ i)
  simpa only [Algebra.smul_def, map_mul, hl, mul_comm] using he

private theorem span_range_mul_unit
    {B : Type*} [CommRing B] {ι : Type*} (z : ι → B) {c : B} (hc : IsUnit c) :
    Ideal.span (Set.range (fun i ↦ z i * c)) = Ideal.span (Set.range z) := by
  simp_rw [Ideal.span_range_eq_iSup, Ideal.span_singleton_mul_right_unit hc]

/-- Enlarge an admissible subalgebra to obtain a differential basis from elements of the
original ring and generators of the maximal ideal in the truncated quotient. -/
theorem exists_popescu_admissible_quotient_basis
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)))) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A₀ ≤ A ∧
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
        ∃ (t r : ℕ) (xs : Fin t → Λ) (ys : Fin r → Λ)
          (a : Fin t → A) (a' : Fin r → A),
          (∀ j, (a j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (xs j))) ∧
          (∀ i, ys i ∈ q ∧ (a' i : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (ys i))) ∧
          (∃ b : Module.Basis (Fin t) (IsLocalRing.ResidueField A)
              (KaehlerDifferential k (IsLocalRing.ResidueField A)),
            ∀ j, b j = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (a j))) ∧
          Ideal.span (Set.range (fun i ↦
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (ys i)))) =
            (q.map (algebraMap Λ (Localization.AtPrime q))).map
              (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) := by
  classical
  have _ := hreg
  let L := Localization.AtPrime q
  let J := q.map (algebraMap Λ L)
  let B := L ⧸ J ^ n
  let f := Ideal.Quotient.mk (J ^ n)
  let π : Λ →+* B := f.comp (algebraMap Λ L)
  let M := J.map f
  obtain ⟨hArt₀, hEft₀, hLoc₀, hFlat₀, hMax₀⟩ := hA₀
  change (IsLocalRing.maximalIdeal A₀).map A₀.val.toRingHom = M at hMax₀
  let : IsArtinianRing A₀ := hArt₀
  let : EssFiniteType k A₀ := hEft₀
  let : IsLocalRing A₀ := hLoc₀
  obtain ⟨t₀, a₀, b₀, hb₀⟩ := exists_residue_differential_basis k A₀
  obtain ⟨r, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsLocalRing.maximalIdeal A₀).fg_of_isNoetherianRing
  have hzmem (i : Fin r) : z i ∈ IsLocalRing.maximalIdeal A₀ := by
    rw [← hz]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hzspan : Ideal.span (Set.range (fun i ↦ (z i : B))) = M := by
    have he := congrArg (Ideal.map A₀.val.toRingHom) hz
    rw [Ideal.map_span, ← Set.range_comp] at he
    exact he.trans hMax₀
  obtain ⟨s, hs, μ, hμ⟩ := common_denominator q n
    (Sum.elim (fun j ↦ (a₀ j : B)) (fun i ↦ (z i : B)))
  change ∀ i, π (μ i) =
    Sum.elim (fun j ↦ (a₀ j : B)) (fun i ↦ (z i : B)) i * π s at hμ
  have hcontract : M.comap π = q := by
    have hpre : (J.map f).comap f = J := by
      rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_of_le_left (Ideal.pow_le_self (by omega))]
    change (J.map f).comap (f.comp (algebraMap Λ L)) = q
    rw [← Ideal.comap_comap, hpre]
    rw [show J = IsLocalRing.maximalIdeal L from
      Localization.AtPrime.map_eq_maximalIdeal]
    exact Localization.AtPrime.under_maximalIdeal
  have hνmem (i : Fin r) : μ (Sum.inr i) ∈ q := by
    rw [← hcontract]
    change π (μ (Sum.inr i)) ∈ M
    rw [hμ (Sum.inr i)]
    apply M.mul_mem_right
    rw [← hMax₀]
    exact Ideal.mem_map_of_mem A₀.val.toRingHom (hzmem i)
  obtain ⟨A, hLoc, hIncl, hAdm, N, hN, c, hc, t, xs, a, hxs, hb⟩ :=
    exists_popescu_denominator_basis_enlargement k Λ p hp q n hn A₀
      ⟨hArt₀, hEft₀, hLoc₀, hFlat₀, hMax₀⟩
      t₀ a₀ b₀ hb₀ s hs (fun j ↦ μ (Sum.inl j)) (fun j ↦ hμ (Sum.inl j))
  let : IsLocalRing A := hLoc
  change (c : B) = (π s) ^ N at hc
  let ys : Fin r → Λ := fun i ↦ μ (Sum.inr i) * s ^ (N - 1)
  let a' : Fin r → A := fun i ↦ (⟨(z i : B), hIncl (z i).property⟩ : A) * c
  have hys (i : Fin r) : π (ys i) = (z i : B) * (π s) ^ N := by
    change π (μ (Sum.inr i) * s ^ (N - 1)) = _
    rw [map_mul, map_pow]
    rw [hμ (Sum.inr i), mul_assoc]
    congr 1
    rw [← pow_succ', Nat.sub_add_cancel hN]
  have hunit : IsUnit ((π s) ^ N) := by
    exact ((IsLocalization.map_units L (⟨s, hs⟩ : q.primeCompl)).map f).pow N
  refine ⟨A, hLoc, hIncl, hAdm, t, r, xs, ys, a, a', hxs, ?_, hb, ?_⟩
  · intro i
    refine ⟨q.mul_mem_right _ (hνmem i), ?_⟩
    change (z i : B) * (c : B) = π (ys i)
    rw [hc, hys]
  · change Ideal.span (Set.range (fun i ↦ π (ys i))) = M
    simp_rw [hys]
    exact (span_range_mul_unit (fun i ↦ (z i : B)) hunit).trans hzspan



end Algebra
