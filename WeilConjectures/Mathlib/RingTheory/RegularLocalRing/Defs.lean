/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Regular local rings are domains

We prove that a regular local ring is a domain (Stacks Project Tag 00NP), by induction on the
embedding dimension. If the maximal ideal `𝔪` is nonzero, prime avoidance gives `x ∈ 𝔪` outside
`𝔪²` and outside every minimal prime. Then `R ⧸ (x)` is regular of one dimension less, hence a
domain, so `(x)` is prime; a minimal prime `p ⊆ (x)` satisfies `p = x p` and vanishes by Nakayama.

## Main results

- `IsRegularLocalRing.isDomain`: a regular local ring is an integral domain.

## Blueprint

- `sk-i-geometry`: regular local rings are domains.
-/
@[expose] public section

open IsLocalRing

universe u

/-- In a Noetherian local ring, if `x ∈ 𝔪 \ 𝔪²` then the maximal ideal of `R ⧸ (x)` needs at
least one generator fewer than `𝔪`: extend the image of `x` in `𝔪 / 𝔪²` to a basis and lift it to
generators of `𝔪` by Nakayama; the generator `x` dies in `R ⧸ (x)`. -/
theorem IsLocalRing.spanFinrank_map_quotient_span_singleton_add_one_le {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x}))).spanFinrank + 1 ≤
      (maximalIdeal R).spanFinrank := by
  classical
  set m := maximalIdeal R
  set v := m.toCotangent ⟨x, hx⟩
  have hv : v ≠ 0 := by rwa [Ne, Ideal.toCotangent_eq_zero]
  have hs : LinearIndepOn (ResidueField R) id {v} := LinearIndepOn.singleton hv
  set B := hs.extend (Set.subset_univ _)
  have hvB : v ∈ B := hs.subset_extend _ rfl
  let b := Module.Basis.extend hs
  have hBfin : B.Finite := Set.toFinite B
  have hBcard : B.ncard = m.spanFinrank := by
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, Module.finrank_eq_nat_card_basis b,
      Nat.card_coe_set_eq]
  let g : CotangentSpace R → m := Function.surjInv m.toCotangent_surjective
  have hg (w) : m.toCotangent (g w) = w := Function.surjInv_eq _ w
  set t : Set m := insert ⟨x, hx⟩ (g '' (B \ {v}))
  have himg : m.toCotangent '' t = B := by
    rw [Set.image_insert_eq, Set.image_image]
    simp only [hg, Set.image_id']
    exact Set.insert_sdiff_singleton.trans (Set.insert_eq_of_mem hvB)
  have hspan : Submodule.span R t = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, himg]
    simpa [b, Module.Basis.coe_extend] using b.span_eq
  have hm : m = Ideal.span (Subtype.val '' t) := by
    change m = Submodule.span R (m.subtype '' t)
    rw [Submodule.span_image, hspan, Submodule.map_top, Submodule.range_subtype]
  have hmap : m.map (Ideal.Quotient.mk (Ideal.span {x})) =
      Ideal.span ((fun w ↦ Ideal.Quotient.mk (Ideal.span {x}) (g w : R)) '' (B \ {v})) := by
    conv_lhs => rw [hm]
    rw [Ideal.map_span, Set.image_image, Set.image_insert_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self x)]
    unfold Ideal.span
    rw [Submodule.span_insert_zero, Set.image_image]
  rw [hmap]
  calc _ ≤ ((fun w ↦ Ideal.Quotient.mk (Ideal.span {x}) (g w : R)) '' (B \ {v})).ncard + 1 := by
        gcongr
        exact Submodule.spanFinrank_span_le_ncard_of_finite ((hBfin.sdiff).image _)
    _ ≤ (B \ {v}).ncard + 1 := by gcongr; exact Set.ncard_image_le hBfin.sdiff
    _ = m.spanFinrank := by
        rw [Set.ncard_sdiff_singleton_add_one hvB hBfin, hBcard]

/-- If `x ∈ 𝔪 \ 𝔪²` in a regular local ring `R`, then `R ⧸ (x)` is a regular local ring whose
maximal ideal needs one generator fewer: `dim R ≤ dim (R ⧸ (x)) + 1` by Krull's height theorem. -/
theorem IsRegularLocalRing.quotient_span_singleton {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ _ : IsLocalRing (R ⧸ Ideal.span {x}), IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (mem_maximalIdeal x).1 hx
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.2 hne
  have hloc : IsLocalRing (R ⧸ Ideal.span {x}) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmax := map_maximalIdeal_of_surjective _ (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
  have h1 := IsLocalRing.spanFinrank_map_quotient_span_singleton_add_one_le hx hx2
  rw [hmax] at h1
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    have := ringKrullDim_le_ringKrullDim_quotient_add_card {x} (by
      simpa [ringJacobson_eq_maximalIdeal] using hx)
    rwa [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] at this
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R := R ⧸ Ideal.span {x})
  have h4 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have h5 : (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {x}) :=
    ringKrullDim_nonneg_of_nontrivial
  set e := (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank
  set d := (maximalIdeal R).spanFinrank
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (R ⧸ Ideal.span {x}) = n := by
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 (ne_bot_of_le_ne_bot WithBot.coe_ne_bot h5)
    rw [← ha] at h3
    have ha' : a ≤ e := by exact_mod_cast h3
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n :=
      ⟨a.toNat, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top e) ha')).symm⟩
    exact ⟨n, ha.symm⟩
  rw [hn] at h2 h3
  rw [← h4] at h2
  have h2' : d ≤ n + 1 := by exact_mod_cast h2
  have h3' : n ≤ e := by exact_mod_cast h3
  refine ⟨hloc, (isRegularLocalRing_iff _).2 ?_, by omega⟩
  rw [hn]
  congr 1
  omega

/-- A regular local ring whose maximal ideal is generated by `n` elements is a domain; this is
proved by induction on `n`, see the module docstring. -/
theorem IsRegularLocalRing.isDomain_of_spanFinrank_eq :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R
  | 0, R, _, _, h => by
    rw [Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing,
      ← isField_iff_maximalIdeal_eq] at h
    let := h.toField
    infer_instance
  | n + 1, R, _, _, h => by
    classical
    set m := maximalIdeal R
    have hdim : ringKrullDim R = (n + 1 : ℕ) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, h]
    have hfin := minimalPrimes.finite_of_isNoetherianRing R
    let f : Option (Ideal R) → Ideal R := fun i ↦ i.elim (m ^ 2) id
    let s : Finset (Option (Ideal R)) := insert none (hfin.toFinset.image some)
    have hnot : ¬ (m : Set R) ⊆ ⋃ i ∈ (s : Set (Option (Ideal R))), (f i : Set R) := by
      rw [Ideal.subset_union_prime none none (by
        rintro (_ | p) hp h1 -
        · exact absurd rfl h1
        · simp only [s, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Set.Finite.mem_toFinset,
            Option.some.injEq, exists_eq_right, false_or] at hp
          exact hp.1.1)]
      rintro ⟨_ | p, hp, hle⟩
      · have : m = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m m
          m.fg_of_isNoetherianRing (by rw [smul_eq_mul, ← pow_two]; exact hle)
          (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top])
        rw [this, Submodule.spanFinrank_bot] at h
        omega
      · simp only [s, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Set.Finite.mem_toFinset,
          Option.some.injEq, exists_eq_right, false_or] at hp
        have hpm : p = m := le_antisymm (le_maximalIdeal hp.1.1.ne_top) hle
        have := Ideal.height_eq_zero_iff.2 (hpm ▸ hp)
        rw [← maximalIdeal_height_eq_ringKrullDim, this] at hdim
        have : (0 : ℕ) = n + 1 := by exact_mod_cast hdim
        omega
    obtain ⟨x, hxm, hx⟩ := Set.not_subset.1 hnot
    simp only [Set.mem_iUnion, not_exists] at hx
    have hx2 : x ∉ m ^ 2 := hx none (by simp [s])
    have hxp (p : Ideal R) (hp : p ∈ minimalPrimes R) : x ∉ p :=
      hx (some p) (by simp only [s, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff,
        reduceCtorEq, Set.mem_image, Finset.mem_coe, Set.Finite.mem_toFinset, Option.some.injEq,
        exists_eq_right, false_or]; exact hp)
    obtain ⟨_, hreg, hrank⟩ := IsRegularLocalRing.quotient_span_singleton hxm hx2
    have := isDomain_of_spanFinrank_eq n (R ⧸ Ideal.span {x}) (by
      have := hrank.trans h
      omega)
    have hprime := (Ideal.Quotient.isDomain_iff_prime _).1 this
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := Ideal.span {x}))
    have hp' : p ∈ minimalPrimes R := hp
    have : p = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m p p.fg_of_isNoetherianRing
        (fun y hy ↦ ?_) (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top])
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 (hpx hy)
      have hz : z ∈ p := (hp'.1.1.mem_or_mem hy).resolve_right (hxp p hp')
      rw [mul_comm]
      exact Submodule.smul_mem_smul hxm hz
    have hbot : (⊥ : Ideal R).IsPrime := this ▸ hp'.1.1
    exact IsDomain.of_bot_isPrime R

/-- A regular local ring is an integral domain. (blueprint: `sk-i-geometry`) -/
instance IsRegularLocalRing.isDomain (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_spanFinrank_eq _ R rfl
