/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Relevance of the points of the projective spectrum

Every point of `ProjectiveSpectrum 𝒜` is a relevant homogeneous prime ideal, so it misses some
homogeneous element of positive degree (`ProjectiveSpectrum.exists_homogeneous_notMem`), and
hence homogeneous elements of arbitrarily large degree
(`ProjectiveSpectrum.exists_homogeneous_notMem_of_le`).

## TODO

When upstreaming, the `local_affine` field of `AlgebraicGeometry.Proj` in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean` repeats the proof of
`ProjectiveSpectrum.exists_homogeneous_notMem` inline and should use it instead.
-/

@[expose] public section

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace ProjectiveSpectrum

/-- Every point of `ProjectiveSpectrum 𝒜` is a relevant homogeneous prime ideal, hence misses
some homogeneous element of positive degree. -/
theorem exists_homogeneous_notMem (x : ProjectiveSpectrum 𝒜) :
    ∃ m > 0, ∃ f ∈ 𝒜 m, f ∉ x.asHomogeneousIdeal := by
  classical
  by_contra! h
  refine x.not_irrelevant_le fun z hz ↦ ?_
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  exact x.1.toIdeal.sum_mem fun k hk ↦
    h k (Nat.pos_of_ne_zero <| by aesop) _ (SetLike.coe_mem _)

/-- Every point of `ProjectiveSpectrum 𝒜` misses homogeneous elements of arbitrarily large
degree. -/
theorem exists_homogeneous_notMem_of_le (x : ProjectiveSpectrum 𝒜) (n : ℕ) :
    ∃ m ≥ n, ∃ f ∈ 𝒜 m, f ∉ x.asHomogeneousIdeal := by
  obtain ⟨d, hd, f, hf, hfx⟩ := x.exists_homogeneous_notMem
  refine ⟨n * d, Nat.le_mul_of_pos_right n hd, f ^ n,
    (by simpa [mul_comm] using SetLike.pow_mem_graded n hf),
    fun h ↦ hfx (x.isPrime.mem_of_pow_mem _ h)⟩

/-- **Graded prime avoidance.** For finitely many points of `ProjectiveSpectrum 𝒜` there is a
homogeneous element of positive degree lying in none of them (Stacks, Tag 00JS). -/
theorem exists_homogeneous_notMem_of_finset (s : Finset (ProjectiveSpectrum 𝒜)) :
    ∃ m > 0, ∃ f ∈ 𝒜 m, ∀ x ∈ s, f ∉ x.asHomogeneousIdeal := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, one_pos, 0, zero_mem _, by simp⟩
  obtain ⟨p, hp⟩ := s.exists_minimal hs
  obtain ⟨d, hd, g, hg, hgs⟩ := ih (s.erase p) (Finset.erase_ssubset hp.prop)
  by_cases hgp : g ∉ p.asHomogeneousIdeal
  · refine ⟨d, hd, g, hg, fun x hx ↦ ?_⟩
    by_cases h : x = p
    · exact h ▸ hgp
    · exact hgs x (Finset.mem_erase.mpr ⟨h, hx⟩)
  rw [not_not] at hgp
  -- every other point contains a homogeneous element outside `p`
  have hx (x : s.erase p) : ∃ e, ∃ h ∈ 𝒜 e, h ∈ x.1.asHomogeneousIdeal ∧
      h ∉ p.asHomogeneousIdeal := by
    have hle : ¬ x.1.asHomogeneousIdeal ≤ p.asHomogeneousIdeal := fun hle ↦
      (Finset.mem_erase.mp x.2).1 (le_antisymm hle (hp.2 (Finset.mem_erase.mp x.2).2 hle))
    obtain ⟨a, hax, hap⟩ := SetLike.not_le_iff_exists.mp hle
    by_contra! H
    refine hap ?_
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    exact p.1.toIdeal.sum_mem fun i _ ↦
      H i _ (SetLike.coe_mem _) (x.1.asHomogeneousIdeal.2 i hax)
  choose e h hh hhx hhp using hx
  obtain ⟨e₀, he₀, h₀, hh₀, hh₀p⟩ := p.exists_homogeneous_notMem
  set E := e₀ + ∑ x ∈ (s.erase p).attach, e x
  set y := h₀ * ∏ x ∈ (s.erase p).attach, h x
  have hy : y ∈ 𝒜 E := SetLike.mul_mem_graded hh₀ (SetLike.prod_mem_graded _ _ _ (fun x _ ↦ hh x))
  have hyp : y ∉ p.asHomogeneousIdeal := by
    refine p.isPrime.mul_notMem hh₀p ?_
    rw [Ideal.IsPrime.prod_mem_iff (hp := p.isPrime)]
    push Not
    exact fun x _ ↦ hhp x
  have hyx (x : s.erase p) : y ∈ x.1.asHomogeneousIdeal :=
    Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ x))
      (hhx x))
  have hE : 0 < E := lt_of_lt_of_le he₀ (Nat.le_add_right _ _)
  refine ⟨d * E, Nat.mul_pos hd hE, g ^ E + y ^ d, add_mem ?_ ?_, fun x hx ↦ ?_⟩
  · simpa [mul_comm] using SetLike.pow_mem_graded E hg
  · simpa using SetLike.pow_mem_graded d hy
  · by_cases hxp : x = p
    · subst hxp
      intro hmem
      exact hyp (x.isPrime.mem_of_pow_mem d ((Ideal.add_mem_iff_right _
        (Ideal.pow_mem_of_mem _ hgp E hE)).mp hmem))
    · have hxe : x ∈ s.erase p := Finset.mem_erase.mpr ⟨hxp, hx⟩
      intro hmem
      exact hgs x hxe (x.isPrime.mem_of_pow_mem E ((Ideal.add_mem_iff_left _
        (Ideal.pow_mem_of_mem _ (hyx ⟨x, hxe⟩) d hd)).mp hmem))

open DirectSum in
/-- A homogeneous ideal which is not contained in an ideal `q` contains a homogeneous element
outside `q`: otherwise all its homogeneous components, hence all its elements, lie in `q`. -/
lemma _root_.HomogeneousIdeal.exists_mem_graded_not_mem (p : HomogeneousIdeal 𝒜) (q : Ideal A)
    (h : ¬ p.toIdeal ≤ q) : ∃ i, ∃ a ∈ 𝒜 i, a ∈ p.toIdeal ∧ a ∉ q := by
  classical
  by_contra H
  push Not at H
  refine h fun x hx ↦ ?_
  rw [← sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun i _ ↦ H i _ (SetLike.coe_mem _) (p.isHomogeneous i hx)

open DirectSum HomogeneousIdeal in
/-- A relevant homogeneous prime misses a homogeneous element of positive degree. -/
lemma exists_pos_mem_graded_not_mem (x : ProjectiveSpectrum 𝒜) :
    ∃ i, 0 < i ∧ ∃ b ∈ 𝒜 i, b ∉ x.asHomogeneousIdeal := by
  obtain ⟨i, b, hb, hbirr, hbx⟩ :=
    (irrelevant 𝒜).exists_mem_graded_not_mem x.asHomogeneousIdeal.toIdeal x.not_irrelevant_le
  refine ⟨i, Nat.pos_of_ne_zero fun hi ↦ hbx ?_, b, hb, hbx⟩
  subst hi
  have h0 : (decompose 𝒜 b 0 : A) = 0 := (mem_irrelevant_iff 𝒜 b).1 hbirr
  rw [decompose_of_mem_same 𝒜 hb] at h0
  rw [h0]
  exact zero_mem _

/-- **Graded prime avoidance.** For finitely many points of `Proj 𝒜`, there is a homogeneous
element of positive degree lying in none of the corresponding homogeneous primes.

Given `a` of degree `d` avoiding the primes of `S` but lying in `p_y`, every `p_x`, `x ∈ S`, is
not contained in `p_y`; with homogeneous `c_x ∈ p_x ∖ p_y` and `b ∉ p_y` of positive degree, the
element `g = b ∏ c_x` of degree `e` and `a^e + g^d` avoid all the primes. -/
theorem exists_mem_graded_forall_not_mem (S : Finset (ProjectiveSpectrum 𝒜)) :
    ∃ m, 0 < m ∧ ∃ f ∈ 𝒜 m, ∀ x ∈ S, f ∉ x.asHomogeneousIdeal := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 0, zero_mem _, by simp⟩
  | @insert y S hy ih =>
    obtain ⟨d, hd, a, ha, haS⟩ := ih
    by_cases hay : a ∉ y.asHomogeneousIdeal
    · exact ⟨d, hd, a, ha, by simpa [hay] using haS⟩
    push Not at hay
    -- the primes `p_x`, `x ∈ S`, not contained in `p_y`
    let S₁ := S.filter fun x ↦ ¬ x.asHomogeneousIdeal.toIdeal ≤ y.asHomogeneousIdeal.toIdeal
    have hc (x : ProjectiveSpectrum 𝒜) (hx : x ∈ S₁) :
        ∃ i, ∃ c ∈ 𝒜 i, c ∈ x.asHomogeneousIdeal.toIdeal ∧ c ∉ y.asHomogeneousIdeal.toIdeal :=
      x.asHomogeneousIdeal.exists_mem_graded_not_mem _ (Finset.mem_filter.1 hx).2
    choose! ic c hcmem hcx hcy using hc
    obtain ⟨ib, hib, b, hb, hby⟩ := exists_pos_mem_graded_not_mem y
    let g := b * ∏ x ∈ S₁, c x
    let e := ib + ∑ x ∈ S₁, ic x
    have hg : g ∈ 𝒜 e := SetLike.mul_mem_graded hb (SetLike.prod_mem_graded 𝒜 ic c hcmem)
    have he : 0 < e := Nat.add_pos_left hib _
    have hgy : g ∉ y.asHomogeneousIdeal := by
      have := y.isPrime
      refine fun hmem ↦ (this.mem_or_mem hmem).elim hby fun hp ↦ ?_
      obtain ⟨x, hx, hcx'⟩ := (Ideal.IsPrime.prod_mem_iff (p := y.asHomogeneousIdeal.toIdeal)).1 hp
      exact hcy x hx hcx'
    have hgx (x : ProjectiveSpectrum 𝒜) (hx : x ∈ S₁) : g ∈ x.asHomogeneousIdeal :=
      Ideal.mul_mem_left _ _ (Ideal.prod_mem _ hx (hcx x hx))
    have hfy : a ^ e + g ^ d ∉ y.asHomogeneousIdeal := by
      intro hmem
      have := y.isPrime
      have h1 : a ^ e ∈ y.asHomogeneousIdeal := Ideal.pow_mem_of_mem _ hay e he
      have h2 : g ^ d ∈ y.asHomogeneousIdeal := by
        simpa using (Ideal.add_mem_iff_right _ h1).1 hmem
      exact hgy (this.mem_of_pow_mem d h2)
    refine ⟨d * e, Nat.mul_pos hd he, a ^ e + g ^ d, ?_, ?_⟩
    · refine add_mem ?_ ?_
      · simpa [mul_comm] using SetLike.pow_mem_graded e ha
      · simpa using SetLike.pow_mem_graded d hg
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hfy
      by_cases hle : x.asHomogeneousIdeal.toIdeal ≤ y.asHomogeneousIdeal.toIdeal
      · exact fun hmem ↦ hfy (hle hmem)
      replace hx : x ∈ S₁ := Finset.mem_filter.2 ⟨hx, hle⟩
      · intro hmem
        have := x.isPrime
        have h2 : g ^ d ∈ x.asHomogeneousIdeal := Ideal.pow_mem_of_mem _ (hgx x hx) d hd
        have h1 : a ^ e ∈ x.asHomogeneousIdeal := by
          simpa using (Ideal.add_mem_iff_left _ h2).1 hmem
        exact haS x (Finset.mem_filter.1 hx).1 (this.mem_of_pow_mem e h1)

end ProjectiveSpectrum
