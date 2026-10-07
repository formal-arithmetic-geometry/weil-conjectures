/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Generic freeness and the rank at the generic point

We record two facts about the rank `Module.rankAtStalk` of a module at a prime.

## Main statements

- `Module.rankAtStalk_comap_ringEquiv`: the rank at a prime is invariant under a ring isomorphism
  together with a compatible additive isomorphism of modules.
- `Module.Finite.exists_free_localizedModule_powers_of_isDomain`: *generic freeness*. A finite
  module `M` over a domain `A` becomes free after inverting a suitable nonzero `r ∈ A`, of rank the
  rank of `M` at the generic point `(0)` of `Spec A`.
-/

@[expose] public section

namespace Module

/-- **The rank at a prime is invariant under ring isomorphisms.** Let `i : R ≃+* R'` and let
`j : M ≃+ M'` be an additive isomorphism from an `R`-module to an `R'`-module with
`j (r • m) = i r • j m`. Then the rank of `M` at the prime `i⁻¹ p` is the rank of `M'` at `p`. -/
theorem rankAtStalk_comap_ringEquiv {R R' M M' : Type*} [CommRing R] [CommRing R']
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (i : R ≃+* R') (j : M ≃+ M')
    (hj : ∀ (r : R) (m : M), j (r • m) = i r • j m) (p : PrimeSpectrum R') :
    rankAtStalk M (p.comap (i : R →+* R')) = rankAtStalk M' p := by
  set q := p.comap (i : R →+* R')
  have hS : q.asIdeal.primeCompl.map i.toMonoidHom = p.asIdeal.primeCompl := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨i.symm x, show i (i.symm x) ∉ p.asIdeal by simpa using hx, by simp⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact hy
  have hmem (s : q.asIdeal.primeCompl) : i s ∈ p.asIdeal.primeCompl := s.2
  have hmem' (s : p.asIdeal.primeCompl) : i.symm s ∈ q.asIdeal.primeCompl := by
    change i (i.symm s) ∉ p.asIdeal
    rw [RingEquiv.apply_symm_apply]
    exact s.2
  let e := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime p.asIdeal) i hS
  let F : LocalizedModule q.asIdeal.primeCompl M → LocalizedModule p.asIdeal.primeCompl M' :=
    fun x ↦ x.liftOn (fun ms ↦ LocalizedModule.mk (j ms.1) ⟨i ms.2, hmem ms.2⟩) (by
      rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨i u, hmem u⟩, ?_⟩
      simp only [Submonoid.smul_def] at hu ⊢
      rw [← hj, ← hj, ← hj, ← hj, hu])
  let G : LocalizedModule p.asIdeal.primeCompl M' → LocalizedModule q.asIdeal.primeCompl M :=
    fun x ↦ x.liftOn (fun ms ↦ LocalizedModule.mk (j.symm ms.1) ⟨i.symm ms.2, hmem' ms.2⟩) (by
      rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨i.symm u, hmem' u⟩, ?_⟩
      simp only [Submonoid.smul_def] at hu ⊢
      apply j.injective
      simp only [hj, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hu])
  have hF (m : M) (s) : F (LocalizedModule.mk m s) = LocalizedModule.mk (j m) ⟨i s, hmem s⟩ :=
    rfl
  have hG (m : M') (s) : G (LocalizedModule.mk m s) =
      LocalizedModule.mk (j.symm m) ⟨i.symm s, hmem' s⟩ :=
    rfl
  let J : LocalizedModule q.asIdeal.primeCompl M ≃+ LocalizedModule p.asIdeal.primeCompl M' :=
    { toFun := F
      invFun := G
      left_inv x := by
        induction x using LocalizedModule.induction_on with
        | h m s => simp [hF, hG]
      right_inv x := by
        induction x using LocalizedModule.induction_on with
        | h m s => simp [hF, hG]
      map_add' x y := by
        induction x using LocalizedModule.induction_on with
        | h m s =>
        induction y using LocalizedModule.induction_on with
        | h m' s' =>
          rw [LocalizedModule.mk_add_mk, hF, hF, hF, LocalizedModule.mk_add_mk]
          congr 1
          · simp [map_add, Submonoid.smul_def, hj]
          · ext
            simp }
  have hJ (x) : J x = F x := rfl
  have he (r : R) (t) : e (Localization.mk r t) = Localization.mk (i r) ⟨i t, hmem t⟩ := by
    simp [e, IsLocalization.ringEquivOfRingEquiv_apply, Localization.mk_eq_mk',
      IsLocalization.map_mk']
  have := _root_.lift_rank_eq_of_equiv_equiv e J e.bijective fun r x ↦ by
    induction r using Localization.induction_on with
    | H rs =>
    induction x using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨r, t⟩ := rs
      rw [LocalizedModule.mk_smul_mk, he]
      rw [hJ, hJ, hF, hF, LocalizedModule.mk_smul_mk, hj]
      congr 1
      ext
      simp
  simpa [rankAtStalk, Module.finrank] using congr_arg Cardinal.toNat this

section IsDomain

variable {A M : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]

/-- **Generic freeness.** Let `M` be a finite module over a domain `A`. Then there is a nonzero
`r ∈ A` such that `M_r` is a free `A_r`-module, of rank the rank of `M` at the generic point `(0)`.
A basis of `M ⊗ Frac(A)` chosen inside `M` gives an injective map `l : A^d → M` whose cokernel is
torsion, hence killed by some nonzero `r` since it is finitely generated; then `l` becomes an
isomorphism after inverting `r`. -/
theorem Finite.exists_free_localizedModule_powers_of_isDomain [Module.Finite A M] :
    ∃ r : A, r ≠ 0 ∧ Module.Free (Localization (.powers r)) (LocalizedModule.Away r M) ∧
      Module.finrank (Localization (.powers r)) (LocalizedModule.Away r M) =
        Module.rankAtStalk (R := A) M ⟨⊥, Ideal.isPrime_bot⟩ := by
  classical
  let K := FractionRing A
  let f := LocalizedModule.mkLinearMap (nonZeroDivisors A) M
  have : Module.Finite K (LocalizedModule (nonZeroDivisors A) M) :=
    Module.Finite.of_isLocalizedModule (nonZeroDivisors A) (Rₚ := K) f
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range f)
  have : Finite b := hli.finite
  have hm (i : b) : ∃ x, f x = i := hb i.2
  choose m hm using hm
  let l := Finsupp.linearCombination A m
  have hl : Function.Injective l := by
    refine LinearIndependent.of_comp f ?_
    have : f ∘ m = ((↑) : b → _) := funext hm
    rw [this]
    exact hli.restrict_scalars' A
  -- every element of `M` has a nonzero multiple in the range of `l`
  have hrange (x : M) : ∃ s ∈ nonZeroDivisors A, s • x ∈ LinearMap.range l := by
    have hx : f x ∈ (Submodule.span A (Set.range m)).localized' K (nonZeroDivisors A) f := by
      rw [Submodule.localized'_span, ← Set.range_comp]
      have : f ∘ m = ((↑) : b → _) := funext hm
      rw [this, Subtype.range_coe, hspan]
      exact Submodule.subset_span ⟨x, rfl⟩
    obtain ⟨y, hy, s, hys⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hys
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hys
    refine ⟨u * s, mul_mem u.2 s.2, ?_⟩
    rw [Finsupp.range_linearCombination, mul_smul, ← Submonoid.smul_def, ← hu]
    exact Submodule.smul_of_tower_mem _ _ hy
  -- a single nonzero `r` with `r • M ⊆ range l`
  choose s hs hsl using hrange
  obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := A) (M := M)
  let r := ∏ x ∈ σ, s x
  have hr : r ∈ nonZeroDivisors A := prod_mem fun x _ ↦ hs x
  have hrl (x : M) : r • x ∈ LinearMap.range l := by
    have : (σ : Set M) ⊆ (LinearMap.range l).comap (r • LinearMap.id) := by
      intro x hx
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq, r, ← Finset.prod_erase_mul σ s hx, mul_smul]
      exact Submodule.smul_mem _ _ (hsl x)
    have := Submodule.span_le.mpr this
    rw [hσ] at this
    exact this trivial
  have key (T : Submonoid A) (hrT : r ∈ T) (hT : T ≤ nonZeroDivisors A) :
      Module.Free (Localization T) (LocalizedModule T M) ∧
        Module.finrank (Localization T) (LocalizedModule T M) = Nat.card b := by
    have : IsDomain (Localization T) := IsLocalization.isDomain_localization hT
    have hbij : Function.Bijective (LocalizedModule.map T l) := by
      refine ⟨LocalizedModule.map_injective T l hl, fun y ↦ ?_⟩
      induction y using LocalizedModule.induction_on with
      | h x t =>
        obtain ⟨z, hz⟩ := hrl x
        refine ⟨LocalizedModule.mk z (⟨r, hrT⟩ * t), ?_⟩
        rw [LocalizedModule.map_mk, hz, LocalizedModule.mk_eq]
        exact ⟨1, by simp [mul_smul, Submonoid.smul_def, smul_comm (t : A) r x]⟩
    let B := (Finsupp.basisSingleOne.ofIsLocalizedModule (Localization T) T
      (LocalizedModule.mkLinearMap T (b →₀ A))).map (LinearEquiv.ofBijective _ hbij)
    exact ⟨.of_basis B, Module.finrank_eq_nat_card_basis B⟩
  refine ⟨r, nonZeroDivisors.ne_zero hr, (key _ (Submonoid.mem_powers r) ?_).1, ?_⟩
  · exact (powers_le_nonZeroDivisors_of_noZeroDivisors (nonZeroDivisors.ne_zero hr))
  · rw [(key _ (Submonoid.mem_powers r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (nonZeroDivisors.ne_zero hr))).2,
      Module.rankAtStalk, (key (Ideal.primeCompl ⊥) (nonZeroDivisors.ne_zero hr)
        fun x hx ↦ mem_nonZeroDivisors_of_ne_zero hx).2]

end IsDomain

end Module
