/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Splitting

/-!
# Auxiliary lemmas for the descent of étaleness along a tame cover

* `RingTheory.InvariantsDescent.nonempty_linearEquiv_pi_of_surjective`: a finite module `M` over
  a Noetherian local ring `(R, 𝔪)` with surjections `M → (R/𝔪ⁿ⁺¹)ᵏ` for all `n`, the first of
  kernel `𝔪 M`, is free of rank `k`.
* Lifts of points `T' → κ(R')` of an étale algebra to `R' ⧸ J` for `J` with `√J = 𝔪_{R'}`:
  joint surjectivity (`surjective_pi_of_injective`), kernel (`mem_map_of_forall_eq_zero`) and
  equivariance (`lift_smul`).
* `RingTheory.InvariantsDescent.surjective_liftPiTop_of_isUnit`: pairwise disjoint points
  `T → B` split `B ⊗ T`.

These are used in `WeilConjectures.RingTheory.Etale.InvariantsDescent`.
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace RingTheory.InvariantsDescent

section Free

variable {R : Type*} [CommRing R]

/-- Let `M` be a finite module over a Noetherian local ring `(R, 𝔪)`. If for every `n` there is a
surjection `M → (R/𝔪ⁿ⁺¹)ᵏ`, and the one for `n = 0` has kernel contained in `𝔪 M`, then `M` is
free of rank `k`. -/
lemma nonempty_linearEquiv_pi_of_surjective [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {k : ℕ}
    (χ : ∀ n : ℕ, M →ₗ[R] (Fin k → R ⧸ maximalIdeal R ^ (n + 1)))
    (hχ : ∀ n, Function.Surjective (χ n))
    (h1 : ∀ x, χ 0 x = 0 → x ∈ maximalIdeal R • (⊤ : Submodule R M)) :
    Nonempty ((Fin k → R) ≃ₗ[R] M) := by
  choose t ht using fun i : Fin k ↦ hχ 0 (Pi.single i 1)
  let f : (Fin k → R) →ₗ[R] M := Fintype.linearCombination R t
  have hχf (n : ℕ) (c : Fin k → R) :
      χ n (f c) = Fintype.linearCombination (R ⧸ maximalIdeal R ^ (n + 1)) (fun i ↦ χ n (t i))
        (fun i ↦ Ideal.Quotient.mk _ (c i)) := by
    ext j
    simp [f, Fintype.linearCombination_apply, Finset.sum_apply, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
      (maximalIdeal_le_jacobson _) fun x _ ↦ ?_
    choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (χ 0 x i)
    have hx : χ 0 (x - f c) = 0 := by
      rw [map_sub, hχf]
      ext i
      simp [Fintype.linearCombination_apply, Finset.sum_apply, ht, Pi.single_apply, hc]
    rw [← add_sub_cancel (f c) x]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self f c))
      (Submodule.mem_sup_right (h1 _ hx))
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have hmem (n : ℕ) (i : Fin k) : x i ∈ maximalIdeal R ^ (n + 1) := by
      let h := Fintype.linearCombination (R ⧸ maximalIdeal R ^ (n + 1)) (fun i ↦ χ n (t i))
      have hh : Function.Surjective h := by
        intro y
        obtain ⟨m, rfl⟩ := hχ n y
        obtain ⟨c, rfl⟩ := hsurj m
        exact ⟨_, (hχf n c).symm⟩
      have := OrzechProperty.injective_of_surjective_endomorphism h hh
        (a₂ := 0) (by rw [← hχf, hx, map_zero, map_zero])
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact congrFun this i
    ext i
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
    rw [Pi.zero_apply, ← Ideal.mem_bot, ← this, Ideal.mem_iInf]
    exact fun n ↦ Ideal.pow_le_pow_right n.le_succ (hmem n i)
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

end Free

section Lift

variable {R' : Type*} [CommRing R'] [IsLocalRing R'] {T' : Type*} [CommRing T'] [Algebra R' T']

/-- The reduction map `R' ⧸ J → κ(R')` for an ideal `J` contained in the maximal ideal. -/
noncomputable abbrev residueOfLE (J : Ideal R') (hJ : J ≤ maximalIdeal R') :
    R' ⧸ J →ₐ[R'] ResidueField R' :=
  Ideal.Quotient.factorₐ R' hJ

lemma residueOfLE_mk (J : Ideal R') (hJ : J ≤ maximalIdeal R') (x : R') :
    residueOfLE J hJ (Ideal.Quotient.mk J x) = residue R' x :=
  rfl

lemma isNilpotent_ker_residueOfLE (J : Ideal R') (hJ : J ≤ maximalIdeal R') {N : ℕ}
    (hN : maximalIdeal R' ^ N ≤ J) :
    IsNilpotent (RingHom.ker (residueOfLE J hJ : R' ⧸ J →+* ResidueField R')) := by
  refine ⟨N, ?_⟩
  have : RingHom.ker (residueOfLE J hJ : R' ⧸ J →+* ResidueField R') =
      (maximalIdeal R').map (Ideal.Quotient.mk J) :=
    Ideal.Quotient.factor_ker hJ
  rw [this, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  exact hN hx

/-- `k` lifts `L j : T' → R' ⧸ J` of pairwise distinct points `T' → κ(R')` define a surjection
`T' → (R' ⧸ J)ᵏ`. -/
lemma surjective_pi_of_injective (J : Ideal R') (hJ : J ≤ maximalIdeal R') {k : ℕ}
    (L : Fin k → (T' →ₐ[R'] R' ⧸ J))
    (hL : Function.Injective fun j ↦ (residueOfLE J hJ).comp (L j)) :
    Function.Surjective (AlgHom.pi L) := by
  let K (j : Fin k) : Ideal T' := RingHom.ker (L j)
  have hcop : Pairwise (Function.onFun IsCoprime K) := by
    intro j l hjl
    obtain ⟨t, ht⟩ : ∃ t, residueOfLE J hJ (L j t) ≠ residueOfLE J hJ (L l t) := by
      by_contra! h
      exact hjl (hL (AlgHom.ext h))
    obtain ⟨sj, hsj⟩ := Ideal.Quotient.mk_surjective (L j t)
    obtain ⟨sl, hsl⟩ := Ideal.Quotient.mk_surjective (L l t)
    have hu : IsUnit (sj - sl) := by
      rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, map_sub, ← residueOfLE_mk J hJ,
        ← residueOfLE_mk J hJ, hsj, hsl, sub_eq_zero]
      exact ht
    set y : T' := algebraMap R' T' ↑hu.unit⁻¹ * (t - algebraMap R' T' sl)
    have hyl : L l y = 0 := by
      simp [y, ← hsl]
    have hyj : L j y = 1 := by
      rw [map_mul, map_sub, AlgHom.commutes, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
        ← hsj, ← map_sub, ← map_mul, IsUnit.val_inv_mul, map_one]
    rw [Function.onFun, Ideal.isCoprime_iff_exists]
    refine ⟨1 - y, ?_, y, hyl, sub_add_cancel 1 y⟩
    rw [RingHom.mem_ker, map_sub, map_one, hyj, sub_self]
  intro z
  choose s hs using fun j ↦ Ideal.Quotient.mk_surjective (z j)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun j ↦ algebraMap R' T' (s j)
  refine ⟨r, funext fun j ↦ ?_⟩
  have := hr j
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
  rw [AlgHom.pi_apply, this, Ideal.Quotient.algebraMap_eq, hs]

attribute [local instance] Module.free_of_flat_of_isLocalRing in
/-- If `T'` is finite flat of rank at most `k` over the local ring `R'`, a surjection
`T' → (R' ⧸ J)ᵏ` given by `k` algebra maps has kernel contained in (hence equal to) `J T'`. -/
lemma mem_map_of_forall_eq_zero [Module.Finite R' T'] [Module.Flat R' T'] {k : ℕ}
    (hk : Module.finrank R' T' ≤ k) (J : Ideal R') (hJ : J ≠ ⊤)
    (L : Fin k → (T' →ₐ[R'] R' ⧸ J)) (hL : Function.Surjective (AlgHom.pi L))
    {t : T'} (ht : ∀ j, L j t = 0) : t ∈ J.map (algebraMap R' T') := by
  let b := Module.finBasis R' T'
  have : Nontrivial (R' ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  let F : (Fin (Module.finrank R' T') → R' ⧸ J) →ₗ[R' ⧸ J] (Fin k → R' ⧸ J) :=
    Fintype.linearCombination (R' ⧸ J) (fun i ↦ AlgHom.pi L (b i))
  have hF (c : Fin (Module.finrank R' T') → R') :
      F (fun i ↦ Ideal.Quotient.mk J (c i)) = AlgHom.pi L (∑ i, c i • b i) := by
    ext j
    simp [F, Fintype.linearCombination_apply, Finset.sum_apply, Algebra.smul_def]
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨s, rfl⟩ := hL y
    exact ⟨fun i ↦ Ideal.Quotient.mk J (b.repr s i), by rw [hF, b.sum_repr]⟩
  have hFb := OrzechProperty.bijective_of_surjective_of_finrank_le F hFs (by simpa using hk)
  have h0 : (fun i ↦ Ideal.Quotient.mk J (b.repr t i)) = 0 := by
    refine hFb.1 ?_
    rw [hF, b.sum_repr, map_zero]
    exact funext ht
  rw [← b.sum_repr t]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h0 i)))

section Equivariant

variable {Γ : Type*} [Group Γ] [MulSemiringAction Γ R'] [MulSemiringAction Γ T']
  [SMulDistribClass Γ R' T']

omit [IsLocalRing R'] in
lemma smul_algebraMap_eq (g : Γ) (r : R') :
    g • algebraMap R' T' r = algebraMap R' T' (g • r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_distrib_smul,
    smul_one]

/-- The unique lift `L : T' → R' ⧸ J` of a `Γ`-invariant point `T' → κ(R')` is `Γ`-equivariant,
if `Γ` acts trivially on `κ(R')`. -/
lemma lift_smul [Algebra.FormallyUnramified R' T'] (J : Ideal R') (hJ : J ≤ maximalIdeal R')
    (hnil : IsNilpotent (RingHom.ker (residueOfLE J hJ : R' ⧸ J →+* ResidueField R')))
    (hJΓ : ∀ (g : Γ) (x : R'), x ∈ J → g • x ∈ J)
    (hκ : ∀ (g : Γ) (x : R'), residue R' (g • x) = residue R' x)
    (L : T' →ₐ[R'] R' ⧸ J)
    (hL : ∀ (g : Γ) (t : T'), residueOfLE J hJ (L (g • t)) = residueOfLE J hJ (L t))
    (g : Γ) (t : T') (x : R') (hx : L t = Ideal.Quotient.mk J x) :
    L (g • t) = Ideal.Quotient.mk J (g • x) := by
  let σ : R' ⧸ J →+* R' ⧸ J :=
    Ideal.quotientMap J (MulSemiringAction.toRingHom Γ R' g) fun y hy ↦ hJΓ g y hy
  have hσ (y : R') : σ (Ideal.Quotient.mk J y) = Ideal.Quotient.mk J (g • y) :=
    Ideal.quotientMap_mk
  let L' : T' →ₐ[R'] R' ⧸ J :=
    { toRingHom := σ.comp (L.toRingHom.comp (MulSemiringAction.toRingHom Γ T' g⁻¹))
      commutes' := fun r ↦ by
        simp [smul_algebraMap_eq, hσ] }
  have hres : (residueOfLE J hJ).comp L' = (residueOfLE J hJ).comp L := by
    ext t'
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (L (g⁻¹ • t'))
    have h1 : L' t' = σ (L (g⁻¹ • t')) := rfl
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h1, ← hy, hσ, residueOfLE_mk, hκ,
      ← residueOfLE_mk J hJ, hy, hL]
  have hLL := Algebra.FormallyUnramified.lift_unique' _ hnil L' L hres
  have h2 : L' (g • t) = σ (L t) := by
    simp [L', inv_smul_smul]
  rw [← hLL, h2, hx, hσ]

end Equivariant

end Lift

section LocalFinite

variable {R R' : Type*} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
  [Algebra R R'] [Algebra.IsIntegral R R']

lemma map_maximalIdeal_le : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' := by
  rw [Ideal.map_le_iff_le_comap]
  exact (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)).ge

/-- For a local ring `R'` integral over the local ring `R`, the maximal ideal of `R'` is the
radical of `𝔪_R R'`. -/
lemma maximalIdeal_le_radical_map :
    maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hle, hP⟩ ↦ ?_
  have hc : (maximalIdeal R).IsMaximal := maximalIdeal.isMaximal R
  have : (P.comap (algebraMap R R')).IsMaximal := by
    rw [← hc.eq_of_le (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      (Ideal.map_le_iff_le_comap.1 hle)]
    exact hc
  exact (eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P this)).ge

end LocalFinite

section Split

/-- If `k` points `ψ j : T → B` with values in a ring `B` are pairwise "disjoint" (for `j ≠ l`
some `ψ j t - ψ l t` is a unit), then `B ⊗ T → Bᵏ` is surjective. -/
lemma surjective_liftPiTop_of_isUnit {R T B : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [CommRing B] [Algebra R B] {k : ℕ} (ψ : Fin k → (T →ₐ[R] B))
    (hψ : ∀ j l, j ≠ l → ∃ t, IsUnit (ψ j t - ψ l t)) :
    Function.Surjective (DepthTwo.liftPiTop ψ) := by
  set Ψ := DepthTwo.liftPiTop ψ
  have hΨ (j : Fin k) (x : B) (t : T) : Ψ (x ⊗ₜ t) j = x * ψ j t := by
    simp [Ψ, DepthTwo.liftPiTop, Algebra.TensorProduct.lift_tmul]
  have hΨa (j : Fin k) (x : B) : Ψ (algebraMap B (B ⊗[R] T) x) j = x := by
    rw [AlgHom.commutes]
    rfl
  let K (j : Fin k) : Ideal (B ⊗[R] T) := RingHom.ker ((Pi.evalAlgHom B (fun _ ↦ B) j).comp Ψ)
  have hK (j : Fin k) (q : B ⊗[R] T) : q ∈ K j ↔ Ψ q j = 0 := Iff.rfl
  have hcop : Pairwise (Function.onFun IsCoprime K) := by
    intro j l hjl
    obtain ⟨t, ht⟩ := hψ j l hjl
    set q : B ⊗[R] T := (1 : B) ⊗ₜ t - algebraMap B _ (ψ l t)
    set y : B ⊗[R] T := algebraMap B _ ↑ht.unit⁻¹ * q
    have hyl : Ψ y l = 0 := by
      simp [y, q, hΨ]
    have hyj : Ψ y j = 1 := by
      simp only [y, q, map_mul, map_sub, Pi.mul_apply, Pi.sub_apply, hΨ, hΨa, one_mul]
      exact ht.val_inv_mul
    rw [Function.onFun, Ideal.isCoprime_iff_exists]
    refine ⟨1 - y, ?_, y, (hK l y).2 hyl, sub_add_cancel 1 y⟩
    rw [hK, map_sub, map_one, Pi.sub_apply, hyj, Pi.one_apply, sub_self]
  intro z
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun j ↦ algebraMap B _ (z j)
  refine ⟨r, funext fun j ↦ ?_⟩
  have := hr j
  rw [hK, map_sub, Pi.sub_apply, hΨa, sub_eq_zero] at this
  exact this

end Split

end RingTheory.InvariantsDescent
