/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Local
public import WeilConjectures.RingTheory.Etale.DepthTwo.LocalToGlobal
public import WeilConjectures.RingTheory.Etale.DepthTwo.Spreading
public import WeilConjectures.RingTheory.Etale.DepthTwo.Rank
public import Mathlib.RingTheory.Ideal.Height

/-!
# Étaleness of the normalization near a section in depth two, in commutative algebra

Let `R₀` be a Noetherian integrally closed domain with fraction field `K`, `B` a smooth Noetherian
`R₀`-algebra with an `R₀`-algebra section `ε : B → R₀`, `B_K` the localization of `B` at the
nonzero elements of `R₀`, `L` a finite étale `B_K`-algebra of rank at most `k` and `T₀` the
integral closure of `B` in `L`. Let `q` be a prime of `R₀` of height at least two and
`P = ε⁻¹(q)` (the image of `q` under the section). Suppose that

* `T₀` is finite étale (of rank at most `k`) over a neighbourhood of every prime `Q ⊆ P` of `B`
  which does not lie over `q` (the normalization is étale over the strict generizations), and
* there are `k` distinct ring maps `L → K` over `ε` (the cover is split along the section).

Then `T₀` is étale over a neighbourhood `D(g)` of `P`
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_two_le_height`). This is the proof of the
claim in the proof of [Stacks 0EYJ], a step of blueprint `sbc-thm-spreading-finite-etale-galois`:
it combines the local statement `RingTheory.DepthTwo.etale_finite_integralClosure` over the local
ring `B_P`, the local-to-global statement `Algebra.etale_finite_tensor_of_forall_isPrime` and the
spreading out `Algebra.exists_etale_integralClosure_of_etale_localization`.
-/

@[expose] public section

universe u

open TensorProduct

namespace RingTheory.DepthTwo

variable {R₀ B Bk L : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀]
  [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B] [IsNoetherianRing B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L]

omit [IsDomain R₀] [IsIntegrallyClosed R₀] [IsNoetherianRing R₀] [Algebra.Smooth R₀ B]
  [IsNoetherianRing B] [Module.Finite Bk L] in
/-- If the integral closure of a localization `B' = B[1/h]` in `L' = L[1/h]` is étale over `B'`,
then so is the base change `B_h ⊗_B T₀` of the integral closure `T₀` of `B` in `L`. -/
lemma etale_away_tensor_integralClosure (h : B) (B' L' : Type*) [CommRing B'] [CommRing L']
    [Algebra B B'] [IsLocalization.Away h B'] [Algebra L L']
    [IsLocalization.Away (algebraMap B L h) L'] [Algebra B' L'] [Algebra B L']
    [IsScalarTower B B' L'] [IsScalarTower B L L']
    (hE : Algebra.Etale B' (integralClosure B' L')) :
    Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B L) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid L (Submonoid.powers h)) L' := by
    rw [Algebra.algebraMapSubmonoid_powers]; infer_instance
  have : Algebra.IsPushout B L B' L' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers h) B' L L'
  have : Algebra.IsPushout B B' L L' := this.symm
  let e : B' ⊗[B] integralClosure B L ≃ₐ[B'] integralClosure B' L' :=
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure B B' L)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization (Submonoid.powers h))).trans
      (Algebra.IsPushout.equiv B B' L L').mapIntegralClosure
  have : Algebra.Etale B' (B' ⊗[B] integralClosure B L) := .of_equiv e.symm
  let eB : B' ≃ₐ[B] Localization.Away h :=
    IsLocalization.algEquiv (Submonoid.powers h) B' (Localization.Away h)
  let : Algebra B' (Localization.Away h) := eB.toRingHom.toAlgebra
  have : IsScalarTower B B' (Localization.Away h) := .of_algebraMap_eq fun b ↦ (eB.commutes b).symm
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange B B' (Localization.Away h)
    (Localization.Away h) (integralClosure B L))

omit [IsNoetherianRing R₀] [Algebra.Smooth R₀ B] [IsNoetherianRing B] in
include Bk in
/-- Distinct ring maps `L → K` over a section `ε : B → R₀` restrict to distinct ring maps
`T₀ → R₀` on the integral closure `T₀` of `B` in `L`, since `R₀` is integrally closed. -/
lemma exists_integralClosure_points (ε : B →ₐ[R₀] R₀) {k : ℕ}
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (φ : Fin k → (L →+* K))
    (hφ : ∀ j, (φ j).comp (algebraMap B L) = (algebraMap R₀ K).comp ε.toRingHom)
    (hφinj : Function.Injective φ) :
    ∃ χ : Fin k → (integralClosure B L →+* R₀),
      (∀ j, (χ j).comp (algebraMap B (integralClosure B L)) = ε.toRingHom) ∧
        Function.Injective χ := by
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
  have hmem (j : Fin k) (t : integralClosure B L) :
      (φ j).comp (integralClosure B L).val.toRingHom t ∈ (algebraMap R₀ K).range := by
    have : IsIntegral R₀ (φ j t) := IsIntegral.map_of_comp_eq ε.toRingHom (φ j) (hφ j).symm t.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    exact ⟨y, hy⟩
  let e : R₀ ≃+* (algebraMap R₀ K).range :=
    RingEquiv.ofBijective (algebraMap R₀ K).rangeRestrict
      ⟨fun x y h ↦ hinj (congrArg Subtype.val h), (algebraMap R₀ K).rangeRestrict_surjective⟩
  let χ (j : Fin k) : integralClosure B L →+* R₀ :=
    e.symm.toRingHom.comp (((φ j).comp (integralClosure B L).val.toRingHom).codRestrict _
      (hmem j))
  have hχ (j : Fin k) (t : integralClosure B L) : algebraMap R₀ K (χ j t) = φ j t := by
    have : e (χ j t) = ((φ j).comp (integralClosure B L).val.toRingHom).codRestrict _
        (hmem j) t := e.apply_symm_apply _
    exact congrArg Subtype.val this
  refine ⟨χ, fun j ↦ RingHom.ext fun b ↦ hinj ?_, fun j l hjl ↦ hφinj ?_⟩
  · rw [RingHom.comp_apply, hχ]
    exact congrArg (· b) (hφ j)
  · have hT (t : integralClosure B L) : φ j t = φ l t := by
      rw [← hχ, ← hχ, hjl]
    refine RingHom.ext fun x ↦ ?_
    have hx : IsIntegral Bk x := Algebra.IsIntegral.isIntegral x
    obtain ⟨⟨_, r, hr, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) x hx
    have h1 := hT ⟨_, hm⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, map_mul] at h1
    have hr0 : φ j (algebraMap B L (algebraMap R₀ B r)) ≠ 0 := by
      rw [← RingHom.comp_apply, hφ]
      simpa using (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr)
    have hjl' : φ j (algebraMap B L (algebraMap R₀ B r)) =
        φ l (algebraMap B L (algebraMap R₀ B r)) := by
      have h1 := congrArg (· (algebraMap R₀ B r)) (hφ j)
      have h2 := congrArg (· (algebraMap R₀ B r)) (hφ l)
      simp only [RingHom.comp_apply] at h1 h2
      rw [h1, h2]
    rw [← hjl'] at h1
    exact mul_left_cancel₀ hr0 h1

include Bk in
/-- **Étaleness of the normalization near a section in depth two** (commutative algebra of the
proof of the claim in the proof of [Stacks 0EYJ], a step of blueprint
`sbc-thm-spreading-finite-etale-galois`). See the module docstring. -/
theorem exists_etale_integralClosure_of_two_le_height (ε : B →ₐ[R₀] R₀) (q : Ideal R₀)
    [q.IsPrime] (hq : 2 ≤ q.height) {k : ℕ}
    (H : ∀ Q : Ideal B, Q.IsPrime → Q ≤ q.comap ε → Q.comap (algebraMap R₀ B) ≠ q →
      ∃ h ∉ Q, Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B L) ∧
        Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B L) ∧
        ∀ p, Module.rankAtStalk (R := Localization.Away h)
          (Localization.Away h ⊗[B] integralClosure B L) p ≤ k)
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (φ : Fin k → (L →+* K))
    (hφ : ∀ j, (φ j).comp (algebraMap B L) = (algebraMap R₀ K).comp ε.toRingHom)
    (hφinj : Function.Injective φ) :
    ∃ g ∉ q.comap ε, ∀ (B' L' : Type u) [CommRing B'] [CommRing L'] [Algebra B B']
      [IsLocalization.Away g B'] [Algebra L L'] [IsLocalization.Away (algebraMap B L g) L']
      [Algebra B' L'] [Algebra B L'] [IsScalarTower B B' L'] [IsScalarTower B L L'],
      Algebra.Etale B' (integralClosure B' L') := by
  set P := q.comap ε
  have hPq : P.comap (algebraMap R₀ B) = q := by
    ext r
    simp [P, Ideal.mem_comap]
  -- the local rings `A = (R₀)_q` and `R = B_P`
  let A := Localization.AtPrime q
  let R := Localization.AtPrime P
  let fAR : A →+* R := Localization.localRingHom q P (algebraMap R₀ B) hPq.symm
  let fRA : R →+* A := Localization.localRingHom P q ε.toRingHom rfl
  let : Algebra A R := fAR.toAlgebra
  let : Algebra R A := fRA.toAlgebra
  have hfAR (r : R₀) : algebraMap A R (algebraMap R₀ A r) = algebraMap B R (algebraMap R₀ B r) :=
    Localization.localRingHom_to_map _ _ _ _ _
  have hfRA (b : B) : algebraMap R A (algebraMap B R b) = algebraMap R₀ A (ε b) :=
    Localization.localRingHom_to_map _ _ _ _ _
  have : IsScalarTower R₀ A R := .of_algebraMap_eq fun r ↦ by
    rw [hfAR, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower A R A := .of_algebraMap_eq' <| IsLocalization.ringHom_ext q.primeCompl <|
    RingHom.ext fun r ↦ by
      change algebraMap R₀ A r = algebraMap R A (algebraMap A R (algebraMap R₀ A r))
      rw [hfAR, hfRA, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have : Algebra.FormallySmooth A R := Algebra.FormallySmooth.localization_base q.primeCompl
  have : Module.Flat A R := (Module.flat_iff_of_isLocalization A q.primeCompl R).2 inferInstance
  have : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization (R := R₀) (S := A) q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  have hdim : 2 ≤ ringKrullDim A := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q A]
    exact (WithBot.coe_le_coe.2 hq : ((2 : ℕ∞) : WithBot ℕ∞) ≤ _)
  -- the cover over `R`
  let M := R ⊗[B] L
  set T₀ := integralClosure B L
  let e₀ : R ⊗[B] T₀ ≃ₐ[R] integralClosure R M :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure B R L)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization P.primeCompl)
  have hunitL (r : R₀) (hr : r ≠ 0) : IsUnit (algebraMap B L (algebraMap R₀ B r)) := by
    rw [IsScalarTower.algebraMap_apply B Bk L]
    exact (IsLocalization.map_units Bk (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
      (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ : nonZeroDivisors R₀)⟩ :
        Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀))).map _
  have hsR (s : q.primeCompl) : IsUnit (algebraMap B R (algebraMap R₀ B s)) := by
    refine (IsLocalization.AtPrime.isUnit_to_map_iff R P _).2 ?_
    intro h
    exact s.2 (by simpa [P, Ideal.mem_comap] using h)
  have hunit (x : A) (hx : x ≠ 0) : IsUnit (algebraMap R M (algebraMap A R x)) := by
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    have hr : r ≠ 0 := by rintro rfl; simp at hx
    have h1 : algebraMap A R (IsLocalization.mk' A r s) * algebraMap B R (algebraMap R₀ B s) =
        algebraMap B R (algebraMap R₀ B r) := by
      rw [← hfAR, ← hfAR, ← map_mul, IsLocalization.mk'_spec]
    have hrM : IsUnit (algebraMap R M (algebraMap B R (algebraMap R₀ B r))) := by
      have : algebraMap R M (algebraMap B R (algebraMap R₀ B r)) =
          Algebra.TensorProduct.includeRight (algebraMap B L (algebraMap R₀ B r)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rw [this]
      exact (hunitL r hr).map _
    rw [← h1, map_mul] at hrM
    exact isUnit_of_mul_isUnit_left hrM
  -- étaleness over the punctured spectrum
  have het : ∀ c ∈ IsLocalRing.maximalIdeal A, c ≠ 0 →
      Algebra.Etale (Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] integralClosure R M) ∧
        Module.Finite (Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] integralClosure R M) ∧
        ∀ p, Module.rankAtStalk (R := Localization.Away (algebraMap A R c))
          (Localization.Away (algebraMap A R c) ⊗[R] integralClosure R M) p ≤ k := by
    intro c hc hc0
    set D := Localization.Away (algebraMap A R c)
    obtain ⟨hE, hF, hk⟩ := Algebra.etale_finite_tensor_of_forall_isPrime (B := B) (D := D)
      (T₀ := T₀) (k := k) fun Q hQ ↦ by
        set Q' := Q.comap (algebraMap B D)
        have hQ'P : Q' ≤ P := by
          have h1 : Q.comap (algebraMap R D) ≤ IsLocalRing.maximalIdeal R :=
            IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime (algebraMap R D) Q).ne_top
          have h2 := Ideal.comap_mono (f := algebraMap B R) h1
          have h3 : (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = P :=
            Localization.AtPrime.under_maximalIdeal (I := P)
          rwa [h3, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq] at h2
        have hQ'q : Q'.comap (algebraMap R₀ B) ≠ q := by
          intro heq
          obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective q.primeCompl c
          have hr : r ∈ q := by
            rw [← hrs] at hc
            exact (IsLocalization.AtPrime.mk'_mem_maximal_iff A q r s).1 hc
          rw [← heq] at hr
          have hrQ : algebraMap B D (algebraMap R₀ B r) ∈ Q := hr
          have hu : IsUnit (algebraMap B D (algebraMap R₀ B r)) := by
            have h1 : algebraMap A R c * algebraMap B R (algebraMap R₀ B s) =
                algebraMap B R (algebraMap R₀ B r) := by
              rw [← hrs, ← hfAR, ← hfAR, ← map_mul, IsLocalization.mk'_spec]
            rw [IsScalarTower.algebraMap_apply B R D, ← h1, map_mul]
            exact (IsLocalization.Away.algebraMap_isUnit _).mul ((hsR s).map _)
          exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hrQ hu)
        obtain ⟨h, hh, hrest⟩ := H Q' (Ideal.comap_isPrime _ _) hQ'P hQ'q
        exact ⟨h, hh, hrest⟩
    let e : D ⊗[R] integralClosure R M ≃ₐ[D] D ⊗[B] T₀ :=
      (Algebra.TensorProduct.congr AlgEquiv.refl e₀.symm).trans
        (Algebra.TensorProduct.cancelBaseChange B R D D T₀)
    refine ⟨.of_equiv e.symm, .equiv e.symm.toLinearEquiv, fun p ↦ ?_⟩
    rw [Module.rankAtStalk_eq_of_equiv e.toLinearEquiv]
    exact hk p
  -- the points along the section
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin k → (integralClosure R M →ₐ[R] A), Function.Injective ψ := by
    obtain ⟨χ, hχ, hχinj⟩ := exists_integralClosure_points (Bk := Bk) ε φ hφ hφinj
    let : Algebra B A := (fRA.comp (algebraMap B R)).toAlgebra
    have : IsScalarTower B R A := .of_algebraMap_eq' rfl
    let χ' (j : Fin k) : T₀ →ₐ[B] A :=
      { toRingHom := (algebraMap R₀ A).comp (χ j)
        commutes' := fun b ↦ by
          change algebraMap R₀ A ((χ j).comp (algebraMap B T₀) b) = fRA (algebraMap B R b)
          rw [hχ]
          exact (hfRA b).symm }
    let ψ' (j : Fin k) : R ⊗[B] T₀ →ₐ[R] A :=
      Algebra.TensorProduct.lift (Algebra.ofId R A) (χ' j) fun _ _ ↦ Commute.all _ _
    refine ⟨fun j ↦ (ψ' j).comp e₀.symm.toAlgHom, fun j l hjl ↦ hχinj ?_⟩
    have hinjA : Function.Injective (algebraMap R₀ A) :=
      IsLocalization.injective A q.primeCompl_le_nonZeroDivisors
    refine RingHom.ext fun t ↦ hinjA ?_
    have := AlgHom.congr_fun hjl (e₀ (1 ⊗ₜ t))
    simpa [ψ', χ'] using this
  obtain ⟨hE, hF⟩ := etale_finite_integralClosure (A := A) (R := R) (M := M) hdim hunit het ψ hψ
  have hE' : Algebra.Etale R (R ⊗[B] T₀) := .of_equiv e₀.symm
  have hF' : Module.Finite R (R ⊗[B] T₀) := .equiv e₀.symm.toLinearEquiv
  exact Algebra.exists_etale_integralClosure_of_etale_localization (R := R₀) (Bk := Bk) P hE' hF'

include Bk in
/-- Variant of `RingTheory.DepthTwo.exists_etale_integralClosure_of_two_le_height` whose
hypothesis on the strict generizations is the étaleness of the integral closure of some
localization `B' = B[1/h]` in `L' = L[1/h]`, which is the form in which it comes from the
normalization of a scheme; finiteness and the rank bound follow from
`RingTheory.DepthTwo.finite_rankAtStalk_le_of_etale`. -/
theorem exists_etale_integralClosure_of_two_le_height' [Algebra.Etale Bk L] (ε : B →ₐ[R₀] R₀)
    (q : Ideal R₀) [q.IsPrime] (hq : 2 ≤ q.height) {k : ℕ}
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p ≤ k)
    (H : ∀ Q : Ideal B, Q.IsPrime → Q ≤ q.comap ε → Q.comap (algebraMap R₀ B) ≠ q →
      ∃ h ∉ Q, ∃ (B' L' : Type u) (_ : CommRing B') (_ : CommRing L') (_ : Algebra B B')
        (_ : IsLocalization.Away h B') (_ : Algebra L L')
        (_ : IsLocalization.Away (algebraMap B L h) L') (_ : Algebra B' L') (_ : Algebra B L')
        (_ : IsScalarTower B B' L') (_ : IsScalarTower B L L'),
        Algebra.Etale B' (integralClosure B' L'))
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (φ : Fin k → (L →+* K))
    (hφ : ∀ j, (φ j).comp (algebraMap B L) = (algebraMap R₀ K).comp ε.toRingHom)
    (hφinj : Function.Injective φ) :
    ∃ g ∉ q.comap ε, ∀ (B' L' : Type u) [CommRing B'] [CommRing L'] [Algebra B B']
      [IsLocalization.Away g B'] [Algebra L L'] [IsLocalization.Away (algebraMap B L g) L']
      [Algebra B' L'] [Algebra B L'] [IsScalarTower B B' L'] [IsScalarTower B L L'],
      Algebra.Etale B' (integralClosure B' L') := by
  refine exists_etale_integralClosure_of_two_le_height (Bk := Bk) ε q hq
    (fun Q hQ hQP hQq ↦ ?_) φ hφ hφinj
  obtain ⟨h, hh, B', L', _, _, _, _, _, _, _, _, _, _, hE⟩ := H Q hQ hQP hQq
  have := etale_away_tensor_integralClosure (L := L) h B' L' hE
  exact ⟨h, hh, this, finite_rankAtStalk_le_of_etale (R₀ := R₀) h hrank⟩

end RingTheory.DepthTwo
