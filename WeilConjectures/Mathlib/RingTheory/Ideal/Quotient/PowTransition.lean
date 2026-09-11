/-
Copyright (c) 2026 The Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Quotients of a local ring by the powers of its maximal ideal

Let `R` be a commutative local ring with maximal ideal `𝔪`.  This file collects the ring-theoretic
facts about the rings `R ⧸ 𝔪 ^ (n + 1)` that the infinitesimal neighbourhoods of a point of a
scheme are built from.

## Main results

- `Ideal.map_pow_mul_map_pow_eq_bot`: the images of `I ^ a` and `I ^ b` in `R ⧸ I ^ r` multiply to
  zero as soon as `r ≤ a + b`.  In particular the image of `I ^ n` in `R ⧸ I ^ (n + 1)`, which is
  the kernel of `R ⧸ I ^ (n + 1) → R ⧸ I ^ n`, is a square-zero ideal annihilated by `I`.
- `IsLocalRing.isLocalRing_quotient_maximalIdeal_pow`: `R ⧸ 𝔪 ^ (n + 1)` is again local, and
  `IsLocalRing.residueFieldQuotientMaximalIdealPow` identifies its residue field with that of `R`.
- `Module.Finite.quotient_pow`: if `R` is a noetherian `k`-algebra with `R = k + I`, then
  `R ⧸ I ^ n` is a finite-dimensional `k`-vector space.
-/

@[expose] public section

universe u

open Submodule

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The images of `I ^ a` and of `I ^ b` in `R ⧸ I ^ r` multiply to zero as soon as
`r ≤ a + b`. -/
theorem map_pow_mul_map_pow_eq_bot {a b r : ℕ} (h : r ≤ a + b) :
    (I ^ a).map (Ideal.Quotient.mk (I ^ r)) * (I ^ b).map (Ideal.Quotient.mk (I ^ r)) = ⊥ := by
  rw [← Ideal.map_mul, ← pow_add, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right h

/-- The image of `I ^ n` in `R ⧸ I ^ (n + 1)` is a square-zero ideal, for `n ≠ 0`. -/
theorem sq_map_pow_eq_bot {n : ℕ} (hn : n ≠ 0) :
    ((I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1)))) ^ 2 = ⊥ := by
  rw [sq]
  exact map_pow_mul_map_pow_eq_bot I (by omega)

/-- The image of `I ^ n` in `R ⧸ I ^ (n + 1)` is annihilated by the image of `I`. -/
theorem map_mul_map_pow_eq_bot (n : ℕ) :
    I.map (Ideal.Quotient.mk (I ^ (n + 1))) *
      (I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1))) = ⊥ := by
  have h := map_pow_mul_map_pow_eq_bot I (a := 1) (b := n) le_rfl
  rwa [pow_one, add_comm 1 n] at h

end Ideal

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem maximalIdeal_pow_ne_top {n : ℕ} (hn : n ≠ 0) : maximalIdeal R ^ n ≠ ⊤ := by
  intro h
  refine (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp ?_)
  rw [← h]
  exact Ideal.pow_le_self hn

instance nontrivial_quotient_maximalIdeal_pow (n : ℕ) :
    Nontrivial (R ⧸ maximalIdeal R ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.mpr (maximalIdeal_pow_ne_top n.succ_ne_zero)

instance isLocalRing_quotient_maximalIdeal_pow (n : ℕ) :
    IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) :=
  .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The maximal ideal of `R ⧸ 𝔪 ^ (n + 1)` is the image of `𝔪`. -/
theorem map_maximalIdeal_quotient_pow (n : ℕ) :
    (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) =
      maximalIdeal (R ⧸ maximalIdeal R ^ (n + 1)) :=
  map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

/-- The residue field of `R ⧸ 𝔪 ^ (n + 1)` is the residue field of `R`. -/
noncomputable def residueFieldQuotientMaximalIdealPow (n : ℕ) :
    ResidueField (R ⧸ maximalIdeal R ^ (n + 1)) ≃+* ResidueField R :=
  (Ideal.quotEquivOfEq (map_maximalIdeal_quotient_pow n).symm).trans
    (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self n.succ_ne_zero))

/-- The transition map `R ⧸ 𝔪 ^ (n + 1) → R ⧸ 𝔪 ^ (m + 1)` is a local ring homomorphism; in
particular an element of `R ⧸ 𝔪 ^ (n + 1)` whose image in `R ⧸ 𝔪 ^ (m + 1)` is a unit is
itself a unit. -/
instance isLocalHom_factor_maximalIdeal_pow {m n : ℕ} (h : m + 1 ≤ n + 1) :
    IsLocalHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right h : maximalIdeal R ^ (n + 1) ≤ maximalIdeal R ^ (m + 1))) :=
  IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective _)

end IsLocalRing

namespace Module.Finite

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- If the composite `k → R → κ(R)` is surjective, then every element of `R` differs from an
element of `k` by an element of the maximal ideal. -/
theorem sub_mem_maximalIdeal_of_residue_surjective [IsLocalRing R]
    (hk : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap k R))) (r : R) :
    ∃ c : k, r - algebraMap k R c ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨c, hc⟩ := hk (IsLocalRing.residue R r)
  rw [RingHom.comp_apply] at hc
  exact ⟨c, (IsLocalRing.residue_eq_zero_iff _).mp (by rw [map_sub, hc, sub_self])⟩

open Submodule in
/-- If `R = k + I` and `R` is noetherian, then `R` is spanned over `k` by finitely many elements
together with `I ^ n`. -/
theorem exists_finset_span_sup_restrictScalars_pow_eq_top [IsNoetherianRing R] (I : Ideal R)
    (hk : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ I) (n : ℕ) :
    ∃ T : Finset R, span k (T : Set R) ⊔ (I ^ n).restrictScalars k = ⊤ := by
  classical
  induction n with
  | zero => exact ⟨∅, by simp⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (I ^ n) : (I ^ n).FG)
    have hGle : span k (G : Set R) ≤ (I ^ n).restrictScalars k := by
      rw [span_le]
      intro g hg
      exact hG ▸ Ideal.subset_span hg
    have key : ∀ y ∈ Submodule.span R (G : Set R),
        y ∈ span k (G : Set R) ⊔ (I ^ (n + 1)).restrictScalars k := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem g hg => exact Submodule.mem_sup_left (Submodule.subset_span hg)
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | smul a z _ hz' =>
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hz'
        obtain ⟨c, hc⟩ := hk a
        have hu' : u ∈ I ^ n := hGle hu
        have h1 : a • u = c • u + (a - algebraMap k R c) * u := by
          rw [smul_eq_mul, Algebra.smul_def]; ring
        rw [← huv, smul_add, h1]
        refine add_mem (add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ c hu)) ?_) ?_
        · refine Submodule.mem_sup_right ?_
          rw [Submodule.restrictScalars_mem, pow_succ']
          exact Ideal.mul_mem_mul hc hu'
        · refine Submodule.mem_sup_right ?_
          rw [Submodule.restrictScalars_mem, smul_eq_mul]
          exact Ideal.mul_mem_left _ _ hv
    replace key : (I ^ n).restrictScalars k ≤
        span k (G : Set R) ⊔ (I ^ (n + 1)).restrictScalars k := fun y hy ↦ key y (hG ▸ hy)
    refine ⟨T ∪ G, le_antisymm le_top ?_⟩
    rw [Finset.coe_union, Submodule.span_union, ← hT]
    exact sup_le (le_sup_of_le_left le_sup_left)
      (key.trans (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))

/-- If `R` is a noetherian `k`-algebra with `R = k + I`, then `R ⧸ I ^ n` is a
finite-dimensional `k`-vector space. -/
theorem quotient_pow [IsNoetherianRing R] (I : Ideal R)
    (hk : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ I) (n : ℕ) :
    Module.Finite k (R ⧸ I ^ n) := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_span_sup_restrictScalars_pow_eq_top I hk n
  refine ⟨⟨T.image (Ideal.Quotient.mk (I ^ n)), le_antisymm le_top ?_⟩⟩
  have key : ∀ u ∈ span k (T : Set R),
      (Ideal.Quotient.mk (I ^ n)) u ∈
        span k ((Ideal.Quotient.mk (I ^ n) : R → R ⧸ I ^ n) '' (T : Set R)) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span ⟨t, ht, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have hca : (Ideal.Quotient.mk (I ^ n)) (c • a) = c • (Ideal.Quotient.mk (I ^ n)) a := by
        simp [Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq, ← RingHom.comp_apply,
          ← IsScalarTower.algebraMap_eq]
      rw [hca]
      exact Submodule.smul_mem _ c ha
  rintro z -
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hr : r ∈ span k (T : Set R) ⊔ (I ^ n).restrictScalars k := hT ▸ Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hr
  rw [← huv, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hv, add_zero, Finset.coe_image]
  exact key u hu

/-- An ideal of `R ⧸ I ^ n` is a finite-dimensional `k`-vector space as soon as `R ⧸ I ^ n` is. -/
theorem ideal_quotient_pow [IsNoetherianRing R] (I : Ideal R)
    (hk : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ I) (n : ℕ) (J : Ideal (R ⧸ I ^ n)) :
    Module.Finite k J := by
  have := quotient_pow I hk n
  exact Module.Finite.of_injective (J.subtype.restrictScalars k) Subtype.val_injective

/-- If `R` is a noetherian local `k`-algebra whose residue field is `k`, then `R ⧸ 𝔪 ^ n` is a
finite-dimensional `k`-vector space. -/
theorem quotient_maximalIdeal_pow [IsLocalRing R] [IsNoetherianRing R]
    (hk : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap k R))) (n : ℕ) :
    Module.Finite k (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
  quotient_pow _ (sub_mem_maximalIdeal_of_residue_surjective hk) n

/-- Any ideal of `R ⧸ 𝔪 ^ n` is a finite-dimensional `k`-vector space, for `R` a noetherian
local `k`-algebra whose residue field is `k`. -/
theorem ideal_quotient_maximalIdeal_pow [IsLocalRing R] [IsNoetherianRing R]
    (hk : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap k R))) (n : ℕ)
    (J : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ n)) :
    Module.Finite k J :=
  ideal_quotient_pow _ (sub_mem_maximalIdeal_of_residue_surjective hk) n J

end Module.Finite
