/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Lift
public import WeilConjectures.Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Finite étale algebras over a punctured neighbourhood of a section in depth two

Let `(R, 𝔪)` be a Noetherian local ring, `I ⊊ R` an ideal (the ideal of a section) and
`a, b ∈ R` such that `[a, b]` is a regular pair on every `R / Iⁿ` and on the `I`-adic completion
`R^`. Let `T` be an `R`-algebra on which `[a, b]` is regular, such that `R_a ⊗ T` and `R_b ⊗ T`
are finite étale of rank at most `k` (geometrically: `Spec T` is a finite étale cover of rank
`≤ k` of `D(a) ∪ D(b)`, and `T` is its ring of functions). If `T` has `k` distinct points with
values in `R / I` (the cover is split along the section), then `T` is finite étale over `R`
(`RingTheory.DepthTwo.etale_and_finite_of_isRegularPair`).

The points lift to the `I`-adic completion (`RingTheory.DepthTwo.exists_liftAlgHom`), they are
pairwise disjoint over `D(a) ∪ D(b)` since the agreement locus of two of them is open and closed
(`Algebra.FormallyUnramified.exists_isIdempotentElem_span_range_sub`) and the idempotents of
`R^` are trivial; so `R^ ⊗ T ≅ (R^)ᵏ`, and `T` is finite étale by faithfully flat descent.
This is the full faithfulness of [Stacks 0EY9] in the form used in the proof of [Stacks 0EYJ].
-/

@[expose] public section

open TensorProduct

namespace RingTheory.DepthTwo

variable {R : Type*} [CommRing R]

section Completion

variable (I : Ideal R)

/-- Over a Noetherian local ring, the `I`-adic completion for a proper ideal `I` has no
idempotents other than `0` and `1`. -/
lemma eq_zero_or_eq_one_of_isIdempotentElem_adicCompletion [IsNoetherianRing R]
    [IsLocalRing R] (hI : I ≠ ⊤) {e : AdicCompletion I R} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have key (e : AdicCompletion I R) (he : IsIdempotentElem e)
      (h0 : AdicCompletion.evalOneₐ I e = 0) : e = 0 := by
    have hmem : e ∈ I.map (algebraMap R (AdicCompletion I R)) := by
      rw [← AdicCompletion.ker_evalOneₐ_eq_map I (IsNoetherian.noetherian I)]
      exact h0
    have := AdicCompletion.isAdicComplete_self I (IsNoetherian.noetherian I)
    have hj := IsAdicComplete.le_jacobson_bot (I.map (algebraMap R (AdicCompletion I R))) hmem
    have hu := (Ideal.mem_jacobson_bot.1 hj) (-1)
    rw [mul_neg_one, neg_add_eq_sub] at hu
    have h : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    exact hu.mul_left_eq_zero.1 h
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hε : IsIdempotentElem (AdicCompletion.evalOneₐ I e) := he.map _
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (AdicCompletion.evalOneₐ I e) with hu | hu
  · right
    have h1 : AdicCompletion.evalOneₐ I e = 1 :=
      hu.mul_left_cancel (by rw [hε.eq, mul_one])
    have := key (1 - e) he.one_sub (by rw [map_sub, map_one, h1, sub_self])
    exact (sub_eq_zero.1 this).symm
  · left
    have h1 : 1 - AdicCompletion.evalOneₐ I e = 1 :=
      hu.mul_left_cancel (by rw [hε.one_sub.eq, mul_one])
    exact key e he (by simpa using h1)

/-- Over a Noetherian local ring, the `I`-adic completion for a proper ideal `I` is faithfully
flat. -/
lemma faithfullyFlat_adicCompletion [IsNoetherianRing R] [IsLocalRing R] (hI : I ≠ ⊤) :
    Module.FaithfullyFlat R (AdicCompletion I R) := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun J hJ htop ↦ ?_⟩
  have hJm : J ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hJ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  let g : AdicCompletion I R →ₗ[R] R ⧸ IsLocalRing.maximalIdeal R :=
    ((Ideal.Quotient.factorₐ R hIm).comp (AdicCompletion.evalOneₐ I)).toLinearMap
  have hg : ∀ x ∈ J • (⊤ : Submodule R (AdicCompletion I R)), g x = 0 := by
    intro x hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr n _ =>
      rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 (hJm hr), zero_mul]
    | add x _ y _ hx hy => rw [map_add, hx, hy, add_zero]
  have h1 := hg 1 (by rw [htop]; exact Submodule.mem_top)
  have : g 1 = 1 := by simp [g]
  exact one_ne_zero (this.symm.trans h1)

end Completion

/-- If `f : M → N` is injective after inverting `a`, and surjective after inverting `a` and after
inverting `b`, with `(a, b)` a regular pair on `M` and `a` regular on `N`, then `f` is bijective:
this is gluing along `D(a) ∪ D(b)` in depth two. -/
lemma bijective_of_isRegularPair {a b : R} {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hM : IsRegularPair a b M) (hN : IsSMulRegular N a)
    (f : M →ₗ[R] N) (hinj : ∀ m, f m = 0 → ∃ n : ℕ, a ^ n • m = 0)
    (hsa : ∀ y, ∃ (n : ℕ) (m : M), f m = a ^ n • y)
    (hsb : ∀ y, ∃ (n : ℕ) (m : M), f m = b ^ n • y) : Function.Bijective f := by
  obtain ⟨hr, hs', hs⟩ := hM
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro m hm
    obtain ⟨n, hn⟩ := hinj m hm
    exact (hr.pow n) (by simpa using hn)
  refine ⟨hf, fun y ↦ ?_⟩
  obtain ⟨k, m₁, h₁⟩ := hsa y
  obtain ⟨l, m₂, h₂⟩ := hsb y
  have h : b ^ l • m₁ = a ^ k • m₂ := hf (by rw [map_smul, map_smul, h₁, h₂, smul_comm])
  obtain ⟨z, rfl, -⟩ := Sequence.exists_eq_smul_of_pow_smul_sub hr hs' hs (N := 0)
    (by rw [pow_zero, one_smul, h, sub_self])
  refine ⟨z, (hN.pow k) ?_⟩
  simp only [← h₁, map_smul]

section Main

variable [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (a b : R)
  (T : Type*) [CommRing T] [Algebra R T]

attribute [local instance] Module.free_of_flat_of_isLocalRing in
/-- A surjective linear map between finite flat modules is bijective if the source has rank at
most the rank of the target at every maximal ideal. -/
lemma bijective_of_surjective_of_rankAtStalk_le {S : Type*} [CommRing S] {M N : Type*}
    [AddCommGroup M] [Module S M] [Module.Finite S M] [Module.Flat S M] [AddCommGroup N]
    [Module S N] [Module.Finite S N] [Module.Flat S N] {φ : M →ₗ[S] N}
    (hs : Function.Surjective φ)
    (h : ∀ (m : Ideal S) [m.IsMaximal],
      Module.rankAtStalk M ⟨m, inferInstance⟩ ≤ Module.rankAtStalk N ⟨m, inferInstance⟩) :
    Function.Bijective φ :=
  bijective_of_localized_maximal φ fun m _ ↦
    OrzechProperty.bijective_of_surjective_of_finrank_le (LocalizedModule.map m.primeCompl φ)
      (LocalizedModule.map_surjective m.primeCompl φ hs) (h m)

variable {a b T}

/-- The base change `ψ_c : R_c ⊗ T → R_c ⊗ B` of an `R`-algebra map `ψ : T → B`. -/
noncomputable abbrev awayMap (c : R) {B : Type*} [CommRing B] [Algebra R B] (ψ : T →ₐ[R] B) :
    Localization.Away c ⊗[R] T →ₐ[Localization.Away c] Localization.Away c ⊗[R] B :=
  Algebra.TensorProduct.map (AlgHom.id _ _) ψ

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- The ideal generated by the differences of two base changes `ψ_c, ψ'_c : R_c ⊗ T → R_c ⊗ B`
is the extension of the ideal generated by the differences of `ψ, ψ'`. -/
lemma span_range_sub_awayMap (c : R) {B : Type*} [CommRing B] [Algebra R B]
    (ψ ψ' : T →ₐ[R] B) :
    Ideal.span (Set.range fun x ↦ awayMap c ψ x - awayMap c ψ' x) =
      (Ideal.span (Set.range fun t ↦ ψ t - ψ' t)).map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] Localization.Away c ⊗[R] B) := by
  refine le_antisymm (Ideal.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    induction x with
    | zero => simp
    | tmul r t =>
      have : awayMap c ψ (r ⊗ₜ t) - awayMap c ψ' (r ⊗ₜ t) =
          (r ⊗ₜ 1) * Algebra.TensorProduct.includeRight (ψ t - ψ' t) := by
        simp only [awayMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.includeRight_apply, map_sub, mul_sub,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      change awayMap c ψ (r ⊗ₜ t) - awayMap c ψ' (r ⊗ₜ t) ∈ _
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨t, rfl⟩))
    | add x y hx hy =>
      simp only [map_add, add_sub_add_comm]
      exact add_mem hx hy
  · rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨1 ⊗ₜ t, ?_⟩
    simp [TensorProduct.tmul_sub]

/-- Two idempotents generating the same principal ideal are equal. -/
lemma eq_of_isIdempotentElem_of_span_eq {S : Type*} [CommRing S] {e f : S}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : Ideal.span {e} = Ideal.span {f}) : e = f := by
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self e)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self f)
  have h1 : e * f = e := by rw [← hx, mul_assoc, hf.eq]
  have h2 : f * e = f := by rw [← hy, mul_assoc, he.eq]
  rw [← h1, mul_comm, h2]

end Main

section Bijective

variable {T : Type*} [CommRing T] [Algebra R T]

/-- The map `(R_c ⊗ B) ⊗ T → (R_c ⊗ B)ᵏ` given by `k` points `ψ_j : T → B`. -/
noncomputable abbrev liftPi (c : R) {B : Type*} [CommRing B] [Algebra R B] {k : ℕ}
    (ψ : Fin k → (T →ₐ[R] B)) :
    (Localization.Away c ⊗[R] B) ⊗[R] T →ₐ[Localization.Away c ⊗[R] B]
      (Fin k → Localization.Away c ⊗[R] B) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun j ↦ (Algebra.TensorProduct.includeRight).comp (ψ j))
    fun _ _ ↦ Commute.all _ _

/-- Over `D(c)`, `k` pairwise disjoint points of a finite étale algebra of rank at most `k`
split it: `(R_c ⊗ B) ⊗ T ≅ (R_c ⊗ B)ᵏ`. -/
lemma bijective_liftPi (c : R) {B : Type*} [CommRing B] [Algebra R B]
    [Algebra.Etale (Localization.Away c) (Localization.Away c ⊗[R] T)]
    [Module.Finite (Localization.Away c) (Localization.Away c ⊗[R] T)]
    {k : ℕ} (hk : ∀ p, Module.rankAtStalk (R := Localization.Away c)
      (Localization.Away c ⊗[R] T) p ≤ k)
    (ψ : Fin k → (T →ₐ[R] B))
    (hψ : ∀ j l, j ≠ l → (Ideal.span (Set.range fun t ↦ ψ j t - ψ l t)).map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] Localization.Away c ⊗[R] B) = ⊤) :
    Function.Bijective (liftPi c ψ) := by
  set Rc := Localization.Away c
  set Bc := Rc ⊗[R] B
  set Q := Bc ⊗[R] T
  set Ψ := liftPi c ψ
  have hΨ (j : Fin k) (x : Bc) (t : T) :
      Ψ (x ⊗ₜ t) j = x * Algebra.TensorProduct.includeRight (ψ j t) := by
    simp [Ψ, liftPi, Algebra.TensorProduct.lift_tmul]
  have hΨa (j : Fin k) (x : Bc) : Ψ (algebraMap Bc Q x) j = x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΨ]
    simp [← Algebra.TensorProduct.one_def]
  let K (j : Fin k) : Ideal Q := RingHom.ker ((Pi.evalAlgHom Bc (fun _ ↦ Bc) j).comp Ψ)
  have hK (j : Fin k) (q : Q) : q ∈ K j ↔ Ψ q j = 0 := Iff.rfl
  have hcop : Pairwise (Function.onFun IsCoprime K) := by
    intro j l hjl
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq, eq_top_iff]
    have hle : (Ideal.span (Set.range fun t ↦ ψ j t - ψ l t)).map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] Bc) ≤
          (K j ⊔ K l).comap (algebraMap Bc Q) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      set d : Bc := Algebra.TensorProduct.includeRight (ψ j t - ψ l t)
      set q : Q := (1 : Bc) ⊗ₜ t - algebraMap Bc Q (Algebra.TensorProduct.includeRight (ψ l t))
      have hq : q ∈ K l := by
        rw [hK, map_sub, Pi.sub_apply, hΨ, hΨa, one_mul, sub_self]
      have hq' : algebraMap Bc Q d - q ∈ K j := by
        rw [hK, map_sub, Pi.sub_apply, hΨa, map_sub, Pi.sub_apply, hΨ, hΨa, one_mul]
        simp [d, TensorProduct.tmul_sub]
      have : algebraMap Bc Q d = (algebraMap Bc Q d - q) + q := by ring
      rw [SetLike.mem_coe, Ideal.mem_comap, this]
      exact add_mem (Ideal.mem_sup_left hq') (Ideal.mem_sup_right hq)
    rw [hψ j l hjl, top_le_iff] at hle
    have h1 : (1 : Bc) ∈ (K j ⊔ K l).comap (algebraMap Bc Q) := hle ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one).ge
  have hsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun j ↦ algebraMap Bc Q (y j)
    refine ⟨r, funext fun j ↦ ?_⟩
    have := hr j
    rw [hK, map_sub, Pi.sub_apply, hΨa, sub_eq_zero] at this
    exact this
  -- `Q` is finite flat of rank at most `k` over `Bc`
  let e : Bc ⊗[Rc] (Rc ⊗[R] T) ≃ₐ[Bc] Q :=
    Algebra.TensorProduct.cancelBaseChange R Rc Bc Bc T
  have : Module.Finite Bc Q := Module.Finite.equiv e.toLinearEquiv
  have : Module.Flat Bc Q := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  refine bijective_of_surjective_of_rankAtStalk_le (φ := Ψ.toLinearMap) hsurj fun m hm ↦ ?_
  have : Nontrivial Bc := ⟨⟨0, 1, fun h ↦ hm.ne_top
    ((Ideal.eq_top_iff_one _).2 (h ▸ m.zero_mem))⟩⟩
  rw [← Module.rankAtStalk_eq_of_equiv e.toLinearEquiv, Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_finrank_of_free (M := Fin k → Bc)]
  have hfin : Module.finrank (Localization.Away c ⊗[R] B) (Fin k → Bc) = k :=
    Module.finrank_fin_fun _
  rw [hfin]
  exact hk _

/-- The map `B ⊗ T → Bᵏ` given by `k` points `ψ_j : T → B`. -/
noncomputable abbrev liftPiTop {B : Type*} [CommRing B] [Algebra R B] {k : ℕ}
    (ψ : Fin k → (T →ₐ[R] B)) : B ⊗[R] T →ₐ[B] (Fin k → B) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.pi ψ) fun _ _ ↦ Commute.all _ _

lemma liftPi_rTensor (c : R) {B : Type*} [CommRing B] [Algebra R B] {k : ℕ}
    (ψ : Fin k → (T →ₐ[R] B)) (x : B ⊗[R] T) :
    liftPi c ψ (AlgebraTensorModule.rTensor R T (TensorProduct.mk R (Localization.Away c) B 1) x)
      = fun j ↦ Algebra.TensorProduct.includeRight (liftPiTop ψ x j) := by
  induction x with
  | zero => ext; simp
  | tmul β t =>
    ext j
    simp [liftPi, liftPiTop, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    ext j
    simp [TensorProduct.tmul_add]

end Bijective

section Main

variable [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} {a b : R}
  {T : Type*} [CommRing T] [Algebra R T]

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Over `D(c)` the localization map `B ⊗ T → (R_c ⊗ B) ⊗ T` and the splitting
`liftPi c ψ` turn the global map `B ⊗ T → Bᵏ` into a map which is injective and surjective up
to powers of `c`. -/
lemma liftPiTop_away (c : R) (hc : IsSMulRegular (AdicCompletion I R) c) {k : ℕ}
    (ψ : Fin k → (T →ₐ[R] AdicCompletion I R)) (hbij : Function.Bijective (liftPi c ψ)) :
    (∀ m, liftPiTop ψ m = 0 → ∃ n : ℕ, c ^ n • m = 0) ∧
      ∀ y, ∃ (n : ℕ) (m : AdicCompletion I R ⊗[R] T), liftPiTop ψ m = c ^ n • y := by
  set B := AdicCompletion I R
  let ι := AlgebraTensorModule.rTensor R T (TensorProduct.mk R (Localization.Away c) B 1)
  have : IsLocalizedModule (Submonoid.powers c) ι :=
    IsLocalizedModule.rTensor (S := Submonoid.powers c)
    (g := TensorProduct.mk R (Localization.Away c) B 1)
  have hiR := injective_includeRight_of_isSMulRegular (M := B) hc
  constructor
  · intro m hm
    have h1 : ι m = ι 0 := by
      apply hbij.1
      rw [liftPi_rTensor, hm, map_zero]
      ext
      simp
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      IsLocalizedModule.exists_of_eq (S := Submonoid.powers c) (f := ι) h1
    exact ⟨n, by simpa [Submonoid.smul_def] using hn⟩
  · intro y
    obtain ⟨q, hq⟩ := hbij.2 fun j ↦ Algebra.TensorProduct.includeRight (y j)
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers c) ι q
    obtain ⟨n, hn⟩ := s.2
    refine ⟨n, m, funext fun j ↦ hiR ?_⟩
    have h3 : liftPi c ψ (ι m) j = Algebra.TensorProduct.includeRight (liftPiTop ψ m j) :=
      congrFun (liftPi_rTensor c ψ m) j
    rw [← h3, ← hs, Submonoid.smul_def, AlgHom.map_smul_of_tower, hq, ← hn]
    simp

/-- **Finite étale algebras over a punctured neighbourhood of a section in depth two.** Let
`(R, 𝔪)` be a Noetherian local ring, `I ≠ R` an ideal and `a, b ∈ R` such that `(a, b)` is a
regular pair on all `R / Iⁿ` and on the `I`-adic completion. Let `T` be an `R`-algebra on which
`[a, b]` is weakly regular and `b` regular, such that `R_a ⊗ T`, `R_b ⊗ T` are finite étale of
rank at most `k`. If there are `k` pairwise distinct `R`-algebra maps `T → R / I`, then `T` is
finite étale over `R`. Geometrically, a finite étale cover of `D(a) ∪ D(b)` which is completely
split along a section extends to a finite étale cover of `Spec R` (a form of [Stacks 0EY9]). -/
theorem etale_and_finite_of_isRegularPair (hI : I ≠ ⊤)
    (hRI : ∀ n, IsRegularPair a b (R ⧸ I ^ n))
    (hB : IsRegularPair a b (AdicCompletion I R))
    (hT : Sequence.IsWeaklyRegular T [a, b]) (hTb : IsSMulRegular T b)
    [Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[R] T)]
    [Module.Finite (Localization.Away a) (Localization.Away a ⊗[R] T)]
    [Algebra.Etale (Localization.Away b) (Localization.Away b ⊗[R] T)]
    [Module.Finite (Localization.Away b) (Localization.Away b ⊗[R] T)]
    {k : ℕ} (hka : ∀ p, Module.rankAtStalk (R := Localization.Away a)
      (Localization.Away a ⊗[R] T) p ≤ k)
    (hkb : ∀ p, Module.rankAtStalk (R := Localization.Away b)
      (Localization.Away b ⊗[R] T) p ≤ k)
    (φ : Fin k → (T →ₐ[R] R ⧸ I)) (hφ : Function.Injective φ) :
    Algebra.Etale R T ∧ Module.Finite R T := by
  set B := AdicCompletion I R
  have : Algebra.FormallyEtale R (Localization.Away a) := .of_isLocalization (Submonoid.powers a)
  have : Algebra.FormallyEtale R (Localization.Away b) := .of_isLocalization (Submonoid.powers b)
  have : Algebra.FormallyEtale R (Localization.Away a ⊗[R] T) := .comp R (Localization.Away a) _
  have : Algebra.FormallyEtale R (Localization.Away b ⊗[R] T) := .comp R (Localization.Away b) _
  choose ψ hψ using fun j ↦ exists_liftAlgHom I a b hRI (φ j)
  obtain ⟨hBa, hBb, hBab⟩ := hB
  -- two distinct points are disjoint over `D(a)` and over `D(b)`
  have hdisj (j l : Fin k) (hjl : j ≠ l) :
      (Ideal.span (Set.range fun t ↦ ψ j t - ψ l t)).map
          (Algebra.TensorProduct.includeRight : B →ₐ[R] Localization.Away a ⊗[R] B) = ⊤ ∧
        (Ideal.span (Set.range fun t ↦ ψ j t - ψ l t)).map
          (Algebra.TensorProduct.includeRight : B →ₐ[R] Localization.Away b ⊗[R] B) = ⊤ := by
    set J := Ideal.span (Set.range fun t ↦ ψ j t - ψ l t)
    obtain ⟨ea, hea, hspa⟩ := Algebra.FormallyUnramified.exists_isIdempotentElem_span_range_sub
      (awayMap a (ψ j)) (awayMap a (ψ l))
    obtain ⟨eb, heb, hspb⟩ := Algebra.FormallyUnramified.exists_isIdempotentElem_span_range_sub
      (awayMap b (ψ j)) (awayMap b (ψ l))
    rw [span_range_sub_awayMap] at hspa hspb
    let ρa : Localization.Away a ⊗[R] B →ₐ[R] Localization.Away (a * b) ⊗[R] B :=
      Algebra.TensorProduct.map (awayLift a (isUnit_algebraMap_away_mul_left a b)) (AlgHom.id R B)
    let ρb : Localization.Away b ⊗[R] B →ₐ[R] Localization.Away (a * b) ⊗[R] B :=
      Algebra.TensorProduct.map (awayLift b (isUnit_algebraMap_away_mul_right a b))
        (AlgHom.id R B)
    have hρa : ρa.comp (Algebra.TensorProduct.includeRight : B →ₐ[R] _) =
        (Algebra.TensorProduct.includeRight : B →ₐ[R] Localization.Away (a * b) ⊗[R] B) := by
      ext x; simp [ρa]
    have hρb : ρb.comp (Algebra.TensorProduct.includeRight : B →ₐ[R] _) =
        (Algebra.TensorProduct.includeRight : B →ₐ[R] Localization.Away (a * b) ⊗[R] B) := by
      ext x; simp [ρb]
    have hcompat : ρa ea = ρb eb := by
      refine eq_of_isIdempotentElem_of_span_eq (hea.map ρa) (heb.map ρb) ?_
      have h1 : Ideal.span {ρa ea} = Ideal.map ρa (Ideal.span {ea}) := by
        rw [Ideal.map_span, Set.image_singleton]
      have h2 : Ideal.span {ρb eb} = Ideal.map ρb (Ideal.span {eb}) := by
        rw [Ideal.map_span, Set.image_singleton]
      rw [h1, h2, ← hspa, ← hspb, Ideal.map_mapₐ, Ideal.map_mapₐ, hρa, hρb]
    obtain ⟨e, hea', heb'⟩ := Sequence.exists_eq_of_isLocalizedModule hBa hBb hBab
      (TensorProduct.mk R (Localization.Away a) B 1)
      (TensorProduct.mk R (Localization.Away b) B 1)
      (TensorProduct.mk R (Localization.Away (a * b)) B 1)
      ((awayLift a (isUnit_algebraMap_away_mul_left a b)).toLinearMap.rTensor B)
      ((awayLift b (isUnit_algebraMap_away_mul_right a b)).toLinearMap.rTensor B)
      (LinearMap.ext fun m ↦ congrArg (· ⊗ₜ[R] m)
        (map_one (awayLift a (isUnit_algebraMap_away_mul_left a b))))
      (LinearMap.ext fun m ↦ congrArg (· ⊗ₜ[R] m)
        (map_one (awayLift b (isUnit_algebraMap_away_mul_right a b)))) ea eb hcompat
    have hiRa := injective_includeRight_of_isSMulRegular (M := B) hBa
    have hiRb := injective_includeRight_of_isSMulRegular (M := B) hBb
    replace hea' : (1 : Localization.Away a) ⊗ₜ[R] e = ea := hea'
    replace heb' : (1 : Localization.Away b) ⊗ₜ[R] e = eb := heb'
    have he : IsIdempotentElem e := by
      apply hiRa
      simp only [map_mul, Algebra.TensorProduct.includeRight_apply, hea']
      exact hea
    rcases eq_zero_or_eq_one_of_isIdempotentElem_adicCompletion I hI he with rfl | rfl
    · exfalso
      refine hjl (hφ ?_)
      have hJ : J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] Localization.Away a ⊗[R] B)
          = ⊥ := by
        rw [hspa, ← hea', TensorProduct.tmul_zero, Ideal.span_singleton_eq_bot]
      have hψjl : ψ j = ψ l := by
        refine AlgHom.ext fun t ↦ ?_
        have : Algebra.TensorProduct.includeRight (ψ j t - ψ l t) =
            (0 : Localization.Away a ⊗[R] B) := by
          rw [← Ideal.mem_bot, ← hJ]
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨t, rfl⟩)
        rw [← map_zero (Algebra.TensorProduct.includeRight : B →ₐ[R] _)] at this
        exact sub_eq_zero.1 (hiRa this)
      rw [← hψ j, ← hψ l, hψjl]
    · refine ⟨?_, ?_⟩
      · rw [hspa, ← hea', Ideal.span_singleton_eq_top]
        exact isUnit_one
      · rw [hspb, ← heb', Ideal.span_singleton_eq_top]
        exact isUnit_one
  -- the splitting over `D(a)` and `D(b)`
  have hbija := bijective_liftPi a hka ψ fun j l h ↦ (hdisj j l h).1
  have hbijb := bijective_liftPi b hkb ψ fun j l h ↦ (hdisj j l h).2
  obtain ⟨hinja, hsa⟩ := liftPiTop_away a hBa ψ hbija
  obtain ⟨-, hsb⟩ := liftPiTop_away b hBb ψ hbijb
  -- the global splitting `B ⊗ T ≅ Bᵏ`
  have hM : IsRegularPair a b (B ⊗[R] T) :=
    isRegularPair_of_isWeaklyRegular hT.isWeaklyRegular_lTensor (hTb.lTensor B)
  have hN : IsSMulRegular (Fin k → B) a := fun x y h ↦ funext fun j ↦ hBa (congrFun h j)
  have hbij := bijective_of_isRegularPair hM hN ((liftPiTop ψ).toLinearMap.restrictScalars R)
    hinja hsa hsb
  let e : B ⊗[R] T ≃ₐ[B] (Fin k → B) := AlgEquiv.ofBijective (liftPiTop ψ) hbij
  have : Algebra.Etale B (B ⊗[R] T) := .of_equiv e.symm
  have : Module.Finite B (B ⊗[R] T) := Module.Finite.equiv e.symm.toLinearEquiv
  have : Module.FaithfullyFlat R B := faithfullyFlat_adicCompletion I hI
  exact ⟨.of_etale_tensorProduct_of_faithfullyFlat B,
    .of_finite_tensorProduct_of_faithfullyFlat B⟩

end Main

end RingTheory.DepthTwo
