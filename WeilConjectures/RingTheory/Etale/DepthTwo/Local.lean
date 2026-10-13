/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Splitting
public import WeilConjectures.RingTheory.IntegrallyClosed.DepthTwo
public import WeilConjectures.RingTheory.Smooth.SectionTruncation

/-!
# Integral closures over a smooth local ring with a section, in depth two

Let `A` be a Noetherian integrally closed local domain of dimension at least two, and let `R` be a
Noetherian local ring which is formally smooth and flat over `A`, with an `A`-algebra section
`R → A` (geometrically: the local ring of a smooth `A`-scheme at the image of a section over the
closed point). Let `M` be an `R`-algebra in which the nonzero elements of `A` are invertible
(geometrically: a cover of the generic fibre) and `T` the integral closure of `R` in `M`. If
`T[1/c]` is finite étale over `R[1/c]` of rank at most `k` for every nonzero `c` in the maximal
ideal of `A` (the normalization is finite étale over the punctured spectrum of `A`), and if `T`
has `k` distinct `R`-algebra maps to `A` (the cover is split along the section), then `T` is
finite étale over `R` (`RingTheory.DepthTwo.etale_finite_integralClosure`).

This is the algebraic content of the proof of the claim in the proof of [Stacks 0EYJ], a step of
blueprint `sbc-thm-spreading-finite-etale-galois`. The proof applies
`RingTheory.DepthTwo.etale_and_finite_of_isRegularPair` to the ring
`T' = {f ∈ M | aⁿ f ∈ T and bᵐ f ∈ T for some n, m}` (`RingTheory.DepthTwo.hartogs`), for a regular
pair `a, b` in the maximal ideal of `A` (which exists by Serre's criterion,
`IsIntegrallyClosed.exists_isWeaklyRegular_pair`): `(a, b)` is regular on `T'` by construction,
`T'[1/a] = T[1/a]`, `T'[1/b] = T[1/b]`, and the points of `T` extend to `T'` since `A` has depth
two. The regularity of `(a, b)` on the infinitesimal neighbourhoods `R / Iⁿ` of the section and on
the completion comes from flatness (`Algebra.FormallySmooth.flat_quotient_pow_ker`). Finally `T'`
is finite over `R`, hence integral, so `T' = T`.
-/

@[expose] public section

open TensorProduct

namespace RingTheory.DepthTwo

section Regular

variable {R : Type*} [CommRing R]

/-- Conversely to `RingTheory.DepthTwo.isRegularPair_of_isWeaklyRegular`, an elementwise regular
pair is a weakly regular sequence. -/
lemma isWeaklyRegular_of_isRegularPair {a b : R} {M : Type*} [AddCommGroup M] [Module R M]
    (h : IsRegularPair a b M) : Sequence.IsWeaklyRegular M [a, b] := by
  obtain ⟨ha, -, hab⟩ := h
  rw [Sequence.isWeaklyRegular_cons_iff, Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨ha, fun q₁ q₂ hq ↦ ?_⟩
  obtain ⟨m₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
  obtain ⟨m₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
  simp only [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq ⊢
  exact hab _ (by rwa [smul_sub])

variable {A N : Type*} [CommRing A] [Algebra A R] [AddCommGroup N] [Module A N] [Module R N]
  [IsScalarTower A R N]

/-- A regular pair of `A` stays regular on a flat `A`-module. -/
lemma isRegularPair_algebraMap_of_flat [Module.Flat A N] {a b : A}
    (hab : Sequence.IsWeaklyRegular A [a, b]) (hb : IsSMulRegular A b) :
    IsRegularPair (algebraMap A R a) (algebraMap A R b) N := by
  have h1 : Sequence.IsWeaklyRegular (N ⊗[A] A) [a, b] := hab.isWeaklyRegular_lTensor
  have h2 : Sequence.IsWeaklyRegular N [a, b] :=
    ((TensorProduct.rid A N).isWeaklyRegular_congr [a, b]).1 h1
  have h3 : Sequence.IsWeaklyRegular N ([a, b].map (algebraMap A R)) :=
    (Sequence.isWeaklyRegular_map_algebraMap_iff R N [a, b]).2 h2
  have hbN : IsSMulRegular N b := by
    intro x y hxy
    apply (TensorProduct.rid A N).symm.injective
    apply hb.lTensor N
    change b • _ = b • _
    rw [← LinearEquiv.map_smul, ← LinearEquiv.map_smul]
    exact congrArg (TensorProduct.rid A N).symm hxy
  refine isRegularPair_of_isWeaklyRegular h3 fun x y hxy ↦ hbN ?_
  simpa only [algebraMap_smul] using hxy

end Regular

section Hartogs

variable {R M : Type*} [CommRing R] [CommRing M] [Algebra R M]

/-- The elements `f` of `M` with `aⁿ f ∈ T` and `bᵐ f ∈ T` for some `n, m`: the functions on the
union of `D(a)` and `D(b)` in `Spec T`, when `a` and `b` are invertible in `M`. -/
def hartogs (a b : R) (T : Subalgebra R M) : Subalgebra R M where
  carrier := {f | (∃ n : ℕ, a ^ n • f ∈ T) ∧ ∃ n : ℕ, b ^ n • f ∈ T}
  mul_mem' {f g} hf hg := by
    obtain ⟨⟨n₁, h₁⟩, ⟨m₁, k₁⟩⟩ := hf
    obtain ⟨⟨n₂, h₂⟩, ⟨m₂, k₂⟩⟩ := hg
    refine ⟨⟨n₁ + n₂, ?_⟩, ⟨m₁ + m₂, ?_⟩⟩
    · convert mul_mem h₁ h₂ using 1
      rw [pow_add, mul_smul, smul_mul_smul_comm, mul_smul]
    · convert mul_mem k₁ k₂ using 1
      rw [pow_add, mul_smul, smul_mul_smul_comm, mul_smul]
  add_mem' {f g} hf hg := by
    obtain ⟨⟨n₁, h₁⟩, ⟨m₁, k₁⟩⟩ := hf
    obtain ⟨⟨n₂, h₂⟩, ⟨m₂, k₂⟩⟩ := hg
    refine ⟨⟨n₁ + n₂, ?_⟩, ⟨m₁ + m₂, ?_⟩⟩
    · convert add_mem (T.smul_mem h₁ (a ^ n₂)) (T.smul_mem h₂ (a ^ n₁)) using 1
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n₂]
    · convert add_mem (T.smul_mem k₁ (b ^ m₂)) (T.smul_mem k₂ (b ^ m₁)) using 1
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm m₂]
  algebraMap_mem' r := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

variable {a b : R} {T : Subalgebra R M}

lemma le_hartogs : T ≤ hartogs a b T := fun f hf ↦ ⟨⟨0, by simpa using hf⟩, ⟨0, by simpa using hf⟩⟩

lemma isRegularPair_hartogs (ha : IsUnit (algebraMap R M a)) (hb : IsUnit (algebraMap R M b)) :
    IsRegularPair a b (hartogs a b T) := by
  have hreg {c : R} (hc : IsUnit (algebraMap R M c)) : IsSMulRegular (hartogs a b T) c := by
    intro x y hxy
    apply Subtype.ext
    have : algebraMap R M c * x = algebraMap R M c * y := by
      simpa [Algebra.smul_def] using congrArg Subtype.val hxy
    exact hc.mul_left_cancel this
  refine ⟨hreg ha, hreg hb, fun t ht ↦ ?_⟩
  obtain ⟨t', -, ht'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ht
  -- `f = t / a = t' / b`
  set f : M := ha.unit⁻¹ * (t : M)
  have hft : algebraMap R M a * f = t := by
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hft' : algebraMap R M b * f = t' := by
    have h1 : (algebraMap R M a) * (t' : M) = algebraMap R M b * t := by
      have := congrArg Subtype.val ht'
      simpa [Algebra.smul_def] using this
    apply ha.mul_left_cancel
    rw [h1, ← hft]
    ring
  have hf : f ∈ hartogs a b T := by
    obtain ⟨⟨n, hn⟩, -⟩ := t.2
    obtain ⟨-, ⟨m, hm⟩⟩ := t'.2
    refine ⟨⟨n + 1, ?_⟩, ⟨m + 1, ?_⟩⟩
    · rw [pow_succ, mul_smul, Algebra.smul_def a, hft]
      exact hn
    · rw [pow_succ, mul_smul, Algebra.smul_def b, hft']
      exact hm
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨⟨f, hf⟩, Submodule.mem_top, ?_⟩
  apply Subtype.ext
  simp [Algebra.smul_def, hft]

/-- The inclusion `T ⊆ hartogs a b T` becomes an isomorphism after inverting `c = a` or `c = b`. -/
lemma bijective_map_inclusion_hartogs {c : R} (hc : c = a ∨ c = b) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (Localization.Away c)
      (Localization.Away c)) (Subalgebra.inclusion (le_hartogs (a := a) (b := b) (T := T)))) := by
  refine ⟨?_, ?_⟩
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := Localization.Away c)
      (Subalgebra.inclusion (le_hartogs (a := a) (b := b) (T := T))).toLinearMap
      (Subalgebra.inclusion_injective (le_hartogs (a := a) (b := b) (T := T)))
  · intro x
    induction x with
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
    | tmul r f =>
      obtain ⟨n, hn⟩ : ∃ n : ℕ, c ^ n • (f : M) ∈ T := by
        rcases hc with rfl | rfl
        · exact f.2.1
        · exact f.2.2
      have hu : IsUnit (algebraMap R (Localization.Away c) (c ^ n)) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit c).pow n
      refine ⟨(hu.unit⁻¹ * r) ⊗ₜ ⟨_, hn⟩, ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      have : (Subalgebra.inclusion le_hartogs ⟨_, hn⟩ : hartogs a b T) = c ^ n • f :=
        Subtype.ext rfl
      rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← mul_assoc,
        IsUnit.mul_val_inv, one_mul]

end Hartogs

section Hartogs

variable {R M : Type*} [CommRing R] [CommRing M] [Algebra R M] {a b : R} {T : Subalgebra R M}
/-- Two `R`-algebra maps on `hartogs a b T` which agree on `T` agree, if `a` is invertible in the
target. -/
lemma algHom_ext_hartogs {C : Type*} [CommRing C] [Algebra R C]
    (ha : IsUnit (algebraMap R C a)) (F₁ F₂ : hartogs a b T →ₐ[R] C)
    (h : F₁.comp (Subalgebra.inclusion le_hartogs) = F₂.comp (Subalgebra.inclusion le_hartogs)) :
    F₁ = F₂ := by
  ext ⟨f, ⟨n, hn⟩, hf⟩
  have h1 := AlgHom.congr_fun h ⟨_, hn⟩
  have h2 : (Subalgebra.inclusion le_hartogs ⟨_, hn⟩ : hartogs a b T) = a ^ n • ⟨f, ⟨n, hn⟩, hf⟩ :=
    Subtype.ext rfl
  rw [AlgHom.comp_apply, AlgHom.comp_apply, h2, map_smul, map_smul] at h1
  simp only [Algebra.smul_def, map_pow] at h1
  exact (ha.pow n).mul_left_cancel h1

end Hartogs

section Main

variable {A R M : Type*} [CommRing A] [CommRing R] [CommRing M] [Algebra R A] [Algebra R M]

/-- The base change isomorphism `R_c ⊗ T ≅ R_c ⊗ hartogs a b T` for `c = a` or `c = b`. -/
noncomputable def hartogsEquiv {a b c : R} (T : Subalgebra R M) (hc : c = a ∨ c = b) :
    Localization.Away c ⊗[R] T ≃ₐ[Localization.Away c] Localization.Away c ⊗[R] hartogs a b T :=
  AlgEquiv.ofBijective _ (bijective_map_inclusion_hartogs (T := T) hc)

lemma hartogsEquiv_tmul {a b c : R} (T : Subalgebra R M) (hc : c = a ∨ c = b) (x) (t : T) :
    hartogsEquiv T hc (x ⊗ₜ t) = x ⊗ₜ Subalgebra.inclusion le_hartogs t := rfl

/-- **Extension of points in depth two.** An `R`-algebra map `T → A` extends to
`hartogs a b T` if `(a, b)` is a regular pair on `A`. -/
lemma exists_extend_hartogs {a b : R} {T : Subalgebra R M} (hA : IsRegularPair a b A)
    (φ : T →ₐ[R] A) :
    ∃ φ' : hartogs a b T →ₐ[R] A, φ'.comp (Subalgebra.inclusion le_hartogs) = φ := by
  let g (c : R) (hc : c = a ∨ c = b) : hartogs a b T →ₐ[R] Localization.Away c ⊗[R] A :=
    ((Algebra.TensorProduct.map (AlgHom.id (Localization.Away c) (Localization.Away c)) φ).comp
      (hartogsEquiv T hc).symm.toAlgHom).restrictScalars R |>.comp
      Algebra.TensorProduct.includeRight
  have hg (c : R) (hc : c = a ∨ c = b) (t : T) :
      g c hc (Subalgebra.inclusion le_hartogs t) = 1 ⊗ₜ φ t := by
    have : (hartogsEquiv T hc).symm (1 ⊗ₜ Subalgebra.inclusion le_hartogs t) = 1 ⊗ₜ t :=
      by rw [← hartogsEquiv_tmul]; exact (hartogsEquiv T hc).symm_apply_apply _
    simp [g, this]
  let ρa := Algebra.TensorProduct.map (awayLift a (isUnit_algebraMap_away_mul_left a b))
    (AlgHom.id R A)
  let ρb := Algebra.TensorProduct.map (awayLift b (isUnit_algebraMap_away_mul_right a b))
    (AlgHom.id R A)
  have hcompat : ρa.comp (g a (.inl rfl)) = ρb.comp (g b (.inr rfl)) := by
    refine algHom_ext_hartogs (isUnit_algebraMap_tensor (isUnit_algebraMap_away_mul_left a b) A)
      _ _ (AlgHom.ext fun t ↦ ?_)
    simp [hg, ρa, ρb]
  obtain ⟨F, hF⟩ := exists_algHom_of_isRegularPair a b hA _ _ hcompat
  refine ⟨F, AlgHom.ext fun t ↦ injective_includeRight_of_isSMulRegular hA.1 ?_⟩
  have := AlgHom.congr_fun hF (Subalgebra.inclusion le_hartogs t)
  simp only [AlgHom.comp_apply] at this ⊢
  rw [this, hg]
  rfl

variable [Algebra A R] [IsScalarTower A R A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
  [IsIntegrallyClosed A]
  [IsLocalRing R] [IsNoetherianRing R] [Algebra.FormallySmooth A R] [Module.Flat A R]

/-- **Finite étale integral closures in depth two, local form** (proof of the claim in the proof
of [Stacks 0EYJ], a step of blueprint `sbc-thm-spreading-finite-etale-galois`). Let `A` be a
Noetherian integrally closed local domain of dimension at least two, `R` a Noetherian local ring,
formally smooth and flat over `A`, with an `A`-algebra section `R → A`, and `M` an `R`-algebra in
which the nonzero elements of `A` are invertible. Let `T` be the integral closure of `R` in `M`.
If `T[1/c]` is finite étale of rank at most `k` over `R[1/c]` for every nonzero `c` in the maximal
ideal of `A`, and `T` has `k` distinct `R`-algebra maps to `A`, then `T` is finite étale over
`R`. -/
theorem etale_finite_integralClosure (hdim : 2 ≤ ringKrullDim A)
    (hunit : ∀ x : A, x ≠ 0 → IsUnit (algebraMap R M (algebraMap A R x))) {k : ℕ}
    (het : ∀ c ∈ IsLocalRing.maximalIdeal A, c ≠ 0 →
      Algebra.Etale (Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] integralClosure R M) ∧
        Module.Finite (Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] integralClosure R M) ∧
        ∀ p, Module.rankAtStalk (R := Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] integralClosure R M) p ≤ k)
    (φ : Fin k → (integralClosure R M →ₐ[R] A)) (hφ : Function.Injective φ) :
    Algebra.Etale R (integralClosure R M) ∧ Module.Finite R (integralClosure R M) := by
  obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := IsIntegrallyClosed.exists_isWeaklyRegular_pair hdim
  have hbA : IsSMulRegular A b := fun x y h ↦ mul_left_cancel₀ hb0 h
  set T' := hartogs (algebraMap A R a) (algebraMap A R b) (integralClosure R M)
  set I := RingHom.ker (algebraMap R A)
  have hsurj : Function.Surjective (algebraMap R A) := fun x ↦
    ⟨algebraMap A R x, Algebra.FormallySmooth.algebraMap_algebraMap_section x⟩
  have hI : I ≠ ⊤ := by
    intro h
    have : (1 : R) ∈ I := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  -- regularity of `(a, b)` on the neighbourhoods of the section and on the completion
  have hRI (n : ℕ) : IsRegularPair (algebraMap A R a) (algebraMap A R b) (R ⧸ I ^ n) := by
    have := Algebra.FormallySmooth.flat_quotient_pow_ker A R n
    exact isRegularPair_algebraMap_of_flat hab hbA
  have : Module.Flat A (AdicCompletion I R) := Module.Flat.trans A R _
  have hB : IsRegularPair (algebraMap A R a) (algebraMap A R b) (AdicCompletion I R) :=
    isRegularPair_algebraMap_of_flat hab hbA
  have hA : IsRegularPair (algebraMap A R a) (algebraMap A R b) A :=
    isRegularPair_algebraMap_of_flat hab hbA
  have hT' : IsRegularPair (algebraMap A R a) (algebraMap A R b) T' :=
    isRegularPair_hartogs (hunit a ha0) (hunit b hb0)
  -- the étale data over `D(a)` and `D(b)`
  have hdata (c : A) (hc : algebraMap A R c = algebraMap A R a ∨
      algebraMap A R c = algebraMap A R b) (hcm : c ∈ IsLocalRing.maximalIdeal A)
      (hc0 : c ≠ 0) :
      Algebra.Etale (Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] T') ∧
        Module.Finite (Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] T') ∧
        ∀ p, Module.rankAtStalk (R := Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] T') p ≤ k := by
    obtain ⟨h1, h2, h3⟩ := het c hcm hc0
    let e := hartogsEquiv (integralClosure R M) hc
    refine ⟨.of_equiv e, .equiv e.toLinearEquiv, fun p ↦ ?_⟩
    rw [← Module.rankAtStalk_eq_of_equiv e.toLinearEquiv]
    exact h3 p
  obtain ⟨hEa, hFa, hka⟩ := hdata a (.inl rfl) ha ha0
  obtain ⟨hEb, hFb, hkb⟩ := hdata b (.inr rfl) hb hb0
  -- the points
  let eA : (R ⧸ I) ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) hsurj
  choose ψ hψ using fun j ↦ exists_extend_hartogs hA (φ j)
  have hψinj : Function.Injective fun j ↦ (eA.symm : A →ₐ[R] R ⧸ I).comp (ψ j) := by
    intro j l hjl
    apply hφ
    rw [← hψ j, ← hψ l]
    congr 1
    ext t
    have := AlgHom.congr_fun hjl t
    simpa using congrArg eA this
  obtain ⟨hE, hF⟩ := etale_and_finite_of_isRegularPair hI hRI hB
    (isWeaklyRegular_of_isRegularPair hT') hT'.2.1 hka hkb _ hψinj
  -- `T' = T`
  have hle : T' ≤ integralClosure R M := by
    intro f hf
    have : IsIntegral R (⟨f, hf⟩ : T') := Algebra.IsIntegral.isIntegral _
    exact this.map T'.val
  have hEq : T' = integralClosure R M := le_antisymm hle le_hartogs
  exact ⟨.of_equiv (Subalgebra.equivOfEq _ _ hEq),
    .equiv (Subalgebra.equivOfEq _ _ hEq).toLinearEquiv⟩

end Main

end RingTheory.DepthTwo
