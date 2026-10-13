/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.NakayamaNilpotent

/-!
# Lifting bases over a local ring with nilpotent maximal ideal

Source: Stacks Project, Algebra, Lemma 10.101.1, Tag 051F
(blueprint: lem-weil-pbc-local-artinian-basis-when-flat).
-/

@[expose] public section

universe u v w

namespace Module

/-- A family in a flat module over a local ring with nilpotent maximal ideal is a basis
if and only if its reductions form a basis over the residue field. No finite generation
of the module or finiteness of the index type is assumed.

Source: Stacks Project, Algebra, Lemma 10.101.1, Tag 051F
(blueprint: lem-weil-pbc-local-artinian-basis-when-flat).

Proof: Let F be the direct sum of copies of R indexed by A, and let phi : F -> M send each
standard basis vector to x a. Modulo the maximal ideal m, F/mF is the direct sum of copies
of R/m, and the reduced map sends the standard basis to the classes of x a. Thus the two
basis assertions say that the reduced map and phi, respectively, are bijective.
If phi is bijective, it carries mF onto mM and induces the required quotient isomorphism.
Conversely, bijectivity of the reduced map implies surjectivity of phi by Nakayama for a
nilpotent ideal (lem-weil-pbc-nakayama-nilpotent), without a finiteness assumption.
Put K = ker phi. The short exact sequence 0 -> K -> F -> M -> 0
(def-weil-pbc-exact-sequence) stays exact after tensoring with R/m, by flatness of M
(def-weil-pbc-flat-ring-map and lem-weil-pbc-flat-quotient-tensor-injective, Tag 00HL).
The natural identifications (R/m) tensor P = P/mP for P = K, F, M
(lem-weil-pbc-tensor-over-quotient-ring) give an exact sequence of the quotients.
Since the reduced phi is injective, K/mK = 0. Nakayama for the nilpotent ideal again
(lem-weil-pbc-nakayama-nilpotent, applied to 0 -> K) gives K = 0. Therefore phi is also
injective, hence bijective, proving the other basis assertion. -/
theorem basis_iff_basisQuotient_of_nilpotent
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hm : IsNilpotent (IsLocalRing.maximalIdeal R)) {A : Type w} (x : A → M) :
    (∃ b : Basis A (R ⧸ IsLocalRing.maximalIdeal R)
      (M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))),
      ∀ a : A, b a = (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (x a)) ↔
    (∃ b : Basis A R M, ∀ a : A, b a = x a) := by
  classical
  set 𝔪 := IsLocalRing.maximalIdeal R
  set q := (𝔪 • (⊤ : Submodule R M)).mkQ
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨n, hn⟩ := hm
    have he : ∀ m : M, TensorProduct.quotTensorEquivQuotSMul M 𝔪
        ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m) = q m := fun m ↦ by
      have := TensorProduct.quotTensorEquivQuotSMul_mk_tmul 𝔪 (1 : R) m
      rw [map_one, one_smul] at this
      exact this
    have hli : LinearIndependent R x := by
      apply IsLocalRing.linearIndependent_of_flat
      rw [linearIndependent_iff']
      intro s g hg i hi
      obtain ⟨c, rfl⟩ : ∃ c : A → R, (fun a ↦ IsLocalRing.residue R (c a)) = g :=
        ⟨fun a ↦ (g a).out, funext fun a ↦ Ideal.Quotient.mk_out (g a)⟩
      have h1 : ∑ a ∈ s, c a •
          (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1 (x a)) = 0 := by
        rw [← hg]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
        rfl
      have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M 𝔪) h1
      erw [map_sum, map_zero] at h2
      simp only [TensorProduct.mk_apply] at h2
      have he' : ∀ a, TensorProduct.quotTensorEquivQuotSMul M 𝔪
          (c a • (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x a) = c a • q (x a) := fun a ↦ by
        rw [← he]; exact LinearEquiv.map_smul _ (c a) _
      erw [Finset.sum_congr rfl fun a _ ↦ he' a] at h2
      have h3 : ∑ a ∈ s, (Ideal.Quotient.mk 𝔪 (c a)) • b a = 0 := by
        rw [← h2]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [hb]
        rfl
      exact linearIndependent_iff'.mp b.linearIndependent s _ h3 i hi
    have hsurj : Function.Surjective (Finsupp.linearCombination R x) := by
      refine RingTheory.surjective_of_surjective_mod_nilpotent R (A →₀ R) M 𝔪 _
        ⟨n + 1, by omega, by rw [pow_succ, hn, zero_mul]; rfl⟩ ?_
      intro z
      have hz : z ∈ (Submodule.span (R ⧸ 𝔪) (Set.range b)).restrictScalars R := by
        rw [b.span_eq]; trivial
      rw [Submodule.restrictScalars_span R (R ⧸ 𝔪) Ideal.Quotient.mk_surjective] at hz
      refine LinearMap.mem_range.mp ((Submodule.span_le (p := LinearMap.range _)).mpr ?_ hz)
      rintro _ ⟨a, rfl⟩
      exact ⟨Submodule.Quotient.mk (Finsupp.single a 1), by
        rw [hb, Submodule.mapQ_apply, Finsupp.linearCombination_single, one_smul]; rfl⟩
    refine ⟨Basis.mk hli ?_, fun a ↦ Basis.mk_apply _ _ _⟩
    rintro m -
    rw [← Finsupp.range_linearCombination]
    exact hsurj m
  · rintro ⟨b, hb⟩
    have hrepr : ∀ m ∈ 𝔪 • (⊤ : Submodule R M), ∀ a, b.repr m a ∈ 𝔪 := by
      intro m hm
      exact Submodule.smul_induction_on hm (fun r hr n _ a ↦ by simpa using 𝔪.mul_mem_right _ hr)
        (fun m n hm hn a ↦ by simpa using 𝔪.add_mem (hm a) (hn a))
    have hli : LinearIndependent (R ⧸ 𝔪) (fun a ↦ q (x a)) := by
      rw [linearIndependent_iff']
      intro s g hg i hi
      obtain ⟨c, rfl⟩ : ∃ c : A → R, (fun a ↦ Ideal.Quotient.mk 𝔪 (c a)) = g :=
        ⟨fun a ↦ (g a).out, funext fun a ↦ Ideal.Quotient.mk_out (g a)⟩
      have hmem : ∑ a ∈ s, c a • b a ∈ 𝔪 • (⊤ : Submodule R M) := by
        rw [← Submodule.Quotient.mk_eq_zero, ← hg]
        change q _ = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [hb]
        rfl
      have := hrepr _ hmem i
      simp only [map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', if_pos hi] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mpr this
    have hsp : ⊤ ≤ Submodule.span (R ⧸ 𝔪) (Set.range fun a ↦ q (x a)) := by
      rintro z -
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ z
      have hm : m ∈ Submodule.span R (Set.range x) := by
        rw [← funext hb, b.span_eq]; trivial
      rw [← Submodule.restrictScalars_mem R,
        Submodule.restrictScalars_span R (R ⧸ 𝔪) Ideal.Quotient.mk_surjective]
      have := Submodule.mem_map_of_mem (f := q) hm
      rwa [Submodule.map_span, ← Set.range_comp] at this
    exact ⟨Basis.mk hli hsp, fun a ↦ by simp [q]⟩

end Module
