/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Lift
public import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# Lifting points with values in an adically complete algebra

This is the variant of `RingTheory.DepthTwo.exists_liftAlgHom` where the target is an arbitrary
`R`-algebra `S`, complete with respect to an ideal `J ⊆ S`, instead of the completion of `R`
itself. Let `a, b ∈ R` such that `(a, b)` is a regular pair on every `S / Jⁿ`, and let `T` be an
`R`-algebra such that `R_a ⊗ T` and `R_b ⊗ T` are formally étale over `R`. Then every
`R`-algebra map `T → S / J` lifts to an `R`-algebra map `T → S`
(`RingTheory.DepthTwo.exists_algHom_lift_of_isAdicComplete`); the lift is unique as soon as `a`
is regular on every `S / Jⁿ` and `R_a ⊗ T` is formally unramified
(`RingTheory.DepthTwo.algHom_eq_of_isAdicComplete`). We also give versions for ring maps
compatible with a ring map `σ : R → S`, which need not be the structure map
(`RingTheory.DepthTwo.exists_ringHom_lift_of_isAdicComplete`).
-/

@[expose] public section

open scoped Pointwise

open TensorProduct

namespace RingTheory.DepthTwo

section Regular

variable {R : Type*} [CommRing R]

/-- Regular pairs are transported along linear equivalences. -/
lemma IsRegularPair.of_linearEquiv {a b : R} {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : IsRegularPair a b M) :
    IsRegularPair a b N := by
  obtain ⟨ha, hb, hab⟩ := h
  refine ⟨fun x y hxy ↦ e.symm.injective (ha ?_), fun x y hxy ↦ e.symm.injective (hb ?_),
    fun n hn ↦ ?_⟩
  · simpa only [← map_smul] using congrArg e.symm hxy
  · simpa only [← map_smul] using congrArg e.symm hxy
  · obtain ⟨m, -, hm⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hn
    have h1 : b • e.symm n ∈ a • (⊤ : Submodule R M) :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨e.symm m, trivial, by rw [← map_smul, hm, map_smul]⟩
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hab _ h1)
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨e y, trivial, by rw [← map_smul, hy, LinearEquiv.apply_symm_apply]⟩

/-- A regular pair of `R` acting on `M` through an `R`-algebra `S`. -/
lemma isRegularPair_algebraMap_iff {S : Type*} [CommRing S] [Algebra R S] {M : Type*}
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] {a b : R} :
    IsRegularPair (algebraMap R S a) (algebraMap R S b) M ↔ IsRegularPair a b M := by
  have hsmul (r : R) (m : M) : algebraMap R S r • m = r • m := algebraMap_smul S r m
  have hreg (r : R) : IsSMulRegular M (algebraMap R S r) ↔ IsSMulRegular M r := by
    simp only [IsSMulRegular, Function.Injective, hsmul]
  have hmem (r : R) (m : M) :
      m ∈ algebraMap R S r • (⊤ : Submodule S M) ↔ m ∈ r • (⊤ : Submodule R M) := by
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, hsmul]
  simp only [IsRegularPair, hreg, hmem, hsmul]

end Regular

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] (J : Ideal S)
  (a b : R) {T : Type*} [CommRing T] [Algebra R T]

/-- The kernel of `S / J^(m+1) → S / J^m` has square zero for `m ≥ 1`. -/
lemma ker_factorₐ_quot_pow_succ_sq {m : ℕ} (hm : 1 ≤ m) :
    RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) m.le_succ)) ^ 2 =
      ⊥ := by
  have hker : RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) m.le_succ))
      = (J ^ m).map (Ideal.Quotient.mk (J ^ (m + 1))) := by
    rw [← Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (I := J) m.le_succ)]
    rfl
  rw [hker, ← Ideal.map_pow, eq_bot_iff, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  rw [← pow_mul] at hx
  exact Ideal.pow_le_pow_right (by omega) hx

/-- The reduction map `R_c ⊗ S / J^(m+1) → R_c ⊗ S / J^m`. -/
noncomputable abbrev reduceAwayQuot (c : R) (m : ℕ) :
    Localization.Away c ⊗[R] (S ⧸ J ^ (m + 1)) →ₐ[R] Localization.Away c ⊗[R] (S ⧸ J ^ m) :=
  Algebra.TensorProduct.map (AlgHom.id R _)
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) m.le_succ))

lemma surjective_reduceAwayQuot (c : R) (m : ℕ) : Function.Surjective (reduceAwayQuot J c m) :=
  LinearMap.lTensor_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := J) m.le_succ))

lemma isNilpotent_ker_reduceAwayQuot (c : R) {m : ℕ} (hm : 1 ≤ m) :
    IsNilpotent (RingHom.ker (reduceAwayQuot J c m)) :=
  isNilpotent_ker_map_id _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := J) m.le_succ))
    (ker_factorₐ_quot_pow_succ_sq J hm)

/-- Two maps `T → S / J^(m+1)` which agree in `S / J^m` agree, if `a` is regular on
`S / J^(m+1)` and `R_a ⊗ T` is formally unramified. -/
lemma eq_of_factorₐ_comp_eq {a : R} {m : ℕ} (ha : IsSMulRegular (S ⧸ J ^ (m + 1)) a)
    [Algebra.FormallyUnramified R (Localization.Away a ⊗[R] T)] (hm : 1 ≤ m)
    (F₁ F₂ : T →ₐ[R] S ⧸ J ^ (m + 1))
    (h : (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) m.le_succ)).comp F₁ =
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) m.le_succ)).comp F₂) :
    F₁ = F₂ := by
  have hinj := injective_includeRight_of_isSMulRegular ha
  have : (Algebra.TensorProduct.includeRight : _ →ₐ[R] Localization.Away a ⊗[R] _).comp F₁ =
      Algebra.TensorProduct.includeRight.comp F₂ := by
    refine algHom_ext_of_formallyUnramified (c := a)
      (isUnit_algebraMap_tensor (IsLocalization.Away.algebraMap_isUnit a) _)
      (reduceAwayQuot J a m) (isNilpotent_ker_reduceAwayQuot J a hm) _ _ ?_
    ext t
    have e := AlgHom.congr_fun h t
    simp only [AlgHom.comp_apply] at e
    simp [e]
  ext t
  exact hinj (AlgHom.congr_fun this t)

/-- One step of the lifting: a map `T → S / J^m` lifts to `T → S / J^(m+1)`, uniquely. -/
lemma existsUnique_liftQuot_succ (hJ : ∀ n, IsRegularPair a b (S ⧸ J ^ n))
    [Algebra.FormallyEtale R (Localization.Away a ⊗[R] T)]
    [Algebra.FormallyEtale R (Localization.Away b ⊗[R] T)]
    {m : ℕ} (hm : 1 ≤ m) (f : T →ₐ[R] S ⧸ J ^ m) :
    ∃! F : T →ₐ[R] S ⧸ J ^ (m + 1),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) m.le_succ)).comp F = f := by
  set fac := Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) m.le_succ)
  -- the lifts on `D(a)` and `D(b)`
  have hlift (c : R) [Algebra.FormallyEtale R (Localization.Away c ⊗[R] T)] :
      ∃ G : Localization.Away c ⊗[R] T →ₐ[R] Localization.Away c ⊗[R] (S ⧸ J ^ (m + 1)),
        (reduceAwayQuot J c m).comp G = Algebra.TensorProduct.map (AlgHom.id R _) f :=
    ⟨Algebra.FormallySmooth.liftOfSurjective _ _ (surjective_reduceAwayQuot J c m)
      (isNilpotent_ker_reduceAwayQuot J c hm),
      Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _⟩
  obtain ⟨Ga, hGa⟩ := hlift a
  obtain ⟨Gb, hGb⟩ := hlift b
  let iRa : T →ₐ[R] Localization.Away a ⊗[R] T := Algebra.TensorProduct.includeRight
  let iRb : T →ₐ[R] Localization.Away b ⊗[R] T := Algebra.TensorProduct.includeRight
  let ρa := awayLift (R := R) a (isUnit_algebraMap_away_mul_left a b)
  let ρb := awayLift (R := R) b (isUnit_algebraMap_away_mul_right a b)
  have hcompat : (Algebra.TensorProduct.map ρa (AlgHom.id R (S ⧸ J ^ (m + 1)))).comp
      (Ga.comp iRa) = (Algebra.TensorProduct.map ρb (AlgHom.id R _)).comp (Gb.comp iRb) := by
    refine algHom_ext_of_formallyUnramified (c := a)
      (isUnit_algebraMap_tensor (isUnit_algebraMap_away_mul_left a b) _)
      (reduceAwayQuot J (a * b) m) (isNilpotent_ker_reduceAwayQuot J _ hm) _ _ ?_
    have e1 : (reduceAwayQuot J (a * b) m).comp (Algebra.TensorProduct.map ρa (AlgHom.id R _)) =
        (Algebra.TensorProduct.map ρa (AlgHom.id R _)).comp (reduceAwayQuot J a m) := by
      exact Algebra.TensorProduct.ext' fun x y ↦ by simp
    have e2 : (reduceAwayQuot J (a * b) m).comp (Algebra.TensorProduct.map ρb (AlgHom.id R _)) =
        (Algebra.TensorProduct.map ρb (AlgHom.id R _)).comp (reduceAwayQuot J b m) := by
      exact Algebra.TensorProduct.ext' fun x y ↦ by simp
    ext t
    have h1 := AlgHom.congr_fun e1 (Ga (iRa t))
    have h2 := AlgHom.congr_fun e2 (Gb (iRb t))
    have h3 := AlgHom.congr_fun hGa (iRa t)
    have h4 := AlgHom.congr_fun hGb (iRb t)
    simp only [AlgHom.comp_apply] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4]
    simp [iRa, iRb]
  obtain ⟨F, hF⟩ := exists_algHom_of_isRegularPair a b (hJ (m + 1)) _ _ hcompat
  have hFf : fac.comp F = f := by
    have hinj := injective_includeRight_of_isSMulRegular (hJ m).1
    ext t
    apply hinj
    calc (Algebra.TensorProduct.includeRight : _ →ₐ[R] Localization.Away a ⊗[R] _) (fac (F t))
        = reduceAwayQuot J a m (Algebra.TensorProduct.includeRight (F t)) := by simp [fac]
      _ = reduceAwayQuot J a m (Ga (iRa t)) := by rw [← AlgHom.comp_apply _ F, hF]; rfl
      _ = Algebra.TensorProduct.includeRight (f t) := by
        rw [← AlgHom.comp_apply, hGa]; simp [iRa]
  exact ⟨F, hFf, fun F' hF' ↦ eq_of_factorₐ_comp_eq J (hJ (m + 1)).1 hm _ _ (hF'.trans hFf.symm)⟩

/-- A map `T → S / J` lifts uniquely to `T → S / J^m` for every `m ≥ 1`. -/
lemma existsUnique_liftQuot (hJ : ∀ n, IsRegularPair a b (S ⧸ J ^ n))
    [Algebra.FormallyEtale R (Localization.Away a ⊗[R] T)]
    [Algebra.FormallyEtale R (Localization.Away b ⊗[R] T)]
    (φ : T →ₐ[R] S ⧸ J) {m : ℕ} (hm : 1 ≤ m) :
    ∃! F : T →ₐ[R] S ⧸ J ^ m, (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (by omega))).comp F
      = φ := by
  induction m, hm using Nat.le_induction with
  | base =>
    let e := Ideal.quotientEquivAlgOfEq R (pow_one J).symm
    have hfe : (Ideal.Quotient.factorₐ R (Ideal.pow_le_self one_ne_zero)).comp e.toAlgHom =
        AlgHom.id R (S ⧸ J) := Ideal.Quotient.algHom_ext _ (by ext; rfl)
    have hef : e.toAlgHom.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_self one_ne_zero)) =
        AlgHom.id R (S ⧸ J ^ 1) := Ideal.Quotient.algHom_ext _ (by ext; rfl)
    refine ⟨e.toAlgHom.comp φ, by beta_reduce; rw [← AlgHom.comp_assoc, hfe, AlgHom.id_comp],
      fun F hF ↦ ?_⟩
    beta_reduce at hF
    rw [← hF, ← AlgHom.comp_assoc, hef, AlgHom.id_comp]
  | succ m hm ih =>
    obtain ⟨f, hf, hfu⟩ := ih
    obtain ⟨F, hF, hFu⟩ := existsUnique_liftQuot_succ J a b hJ hm f
    have hcomp : (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (by omega))).comp
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) m.le_succ)) =
        Ideal.Quotient.factorₐ R (Ideal.pow_le_self (n := m + 1) (by omega)) :=
      Ideal.Quotient.factorₐ_comp _ _ _
    refine ⟨F, by beta_reduce; rw [← hcomp, AlgHom.comp_assoc, hF, hf], fun F' hF' ↦ hFu F' ?_⟩
    beta_reduce at hF' ⊢
    refine hfu _ ?_
    beta_reduce
    rw [← AlgHom.comp_assoc, hcomp, hF']

/-- **Lifting points to an adically complete algebra.** If `(a, b)` is a regular pair on all
`S / Jⁿ`, `S` is `J`-adically complete and `R_a ⊗ T`, `R_b ⊗ T` are formally étale over `R`,
then every `R`-algebra map `T → S / J` lifts to an `R`-algebra map `T → S`. -/
theorem exists_algHom_lift_of_isAdicComplete [IsAdicComplete J S]
    (hJ : ∀ n, IsRegularPair a b (S ⧸ J ^ n))
    [Algebra.FormallyEtale R (Localization.Away a ⊗[R] T)]
    [Algebra.FormallyEtale R (Localization.Away b ⊗[R] T)]
    (φ : T →ₐ[R] S ⧸ J) :
    ∃ ψ : T →ₐ[R] S, (Ideal.Quotient.mkₐ R J).comp ψ = φ := by
  choose L hL hLu using fun n : ℕ ↦ existsUnique_liftQuot J a b hJ φ (m := n + 1) (by omega)
  let f (n : ℕ) : T →ₐ[R] S ⧸ J ^ n :=
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) n.le_succ)).comp (L n)
  have hf {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    have : (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := J) (by omega : m + 1 ≤ n + 1))
        ).comp (L n) = L m := by
      refine hLu m _ ?_
      beta_reduce
      rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
      exact hL n
    simp only [f, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
    rw [← this, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  refine ⟨IsAdicComplete.liftAlgHom J f hf, ?_⟩
  ext t
  have h1 := AlgHom.congr_fun (IsAdicComplete.mkₐ_comp_liftAlgHom J f hf 1) t
  have h2 := AlgHom.congr_fun (hL 1) t
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, f] at h1 h2 ⊢
  calc Ideal.Quotient.mk J (IsAdicComplete.liftAlgHom J f hf t)
      = Ideal.Quotient.factorₐ R (Ideal.pow_le_self (I := J) one_ne_zero)
          (Ideal.Quotient.mk (J ^ 1) (IsAdicComplete.liftAlgHom J f hf t)) := rfl
    _ = φ t := by rw [h1, ← AlgHom.comp_apply, Ideal.Quotient.factorₐ_comp, h2]

/-- **Uniqueness of lifts to an adically complete algebra.** Two `R`-algebra maps `T → S` which
agree modulo `J` agree, if `S` is `J`-adically complete, `a` is regular on every `S / Jⁿ` and
`R_a ⊗ T` is formally unramified over `R`. -/
theorem algHom_eq_of_isAdicComplete [IsAdicComplete J S] {a : R}
    (ha : ∀ n, IsSMulRegular (S ⧸ J ^ n) a)
    [Algebra.FormallyUnramified R (Localization.Away a ⊗[R] T)] (ψ₁ ψ₂ : T →ₐ[R] S)
    (h : (Ideal.Quotient.mkₐ R J).comp ψ₁ = (Ideal.Quotient.mkₐ R J).comp ψ₂) : ψ₁ = ψ₂ := by
  refine IsAdicComplete.algHom_ext J fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (S ⧸ J ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext
    exact Subsingleton.elim _ _
  induction n, hn using Nat.le_induction with
  | base =>
    ext t
    have := AlgHom.congr_fun h t
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this ⊢
    rw [Ideal.Quotient.eq] at this ⊢
    simpa using this
  | succ m hm ih =>
    refine eq_of_factorₐ_comp_eq J (ha (m + 1)) hm _ _ ?_
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk, ih]

/-- **Lifting ring maps compatible with `σ`.** Version of
`RingTheory.DepthTwo.exists_algHom_lift_of_isAdicComplete` for a ring `X` with a ring map
`σ : R → X`, which is not assumed to be an algebra structure. -/
theorem exists_ringHom_lift_of_isAdicComplete {X : Type*} [CommRing X] (σ : R →+* X)
    (J : Ideal X) [IsAdicComplete J X] (hJ : ∀ n, IsRegularPair (σ a) (σ b) (X ⧸ J ^ n))
    [Algebra.FormallyEtale R (Localization.Away a ⊗[R] T)]
    [Algebra.FormallyEtale R (Localization.Away b ⊗[R] T)]
    (φ : T →+* X ⧸ J) (hφ : φ.comp (algebraMap R T) = (Ideal.Quotient.mk J).comp σ) :
    ∃ ψ : T →+* X, ψ.comp (algebraMap R T) = σ ∧ (Ideal.Quotient.mk J).comp ψ = φ := by
  let := σ.toAlgebra
  have hJ' (n : ℕ) : IsRegularPair a b (X ⧸ J ^ n) :=
    isRegularPair_algebraMap_iff (S := X).1 (hJ n)
  let φ' : T →ₐ[R] X ⧸ J :=
    { φ with commutes' := fun r ↦ RingHom.congr_fun hφ r }
  obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_isAdicComplete J a b hJ' φ'
  refine ⟨ψ.toRingHom, RingHom.ext fun r ↦ ψ.commutes r, RingHom.ext fun t ↦ ?_⟩
  exact AlgHom.congr_fun hψ t

/-- **Uniqueness of ring maps compatible with `σ`.** Version of
`RingTheory.DepthTwo.algHom_eq_of_isAdicComplete` for a ring map `σ : R → X`. -/
theorem ringHom_eq_of_isAdicComplete {X : Type*} [CommRing X] (σ : R →+* X)
    (J : Ideal X) [IsAdicComplete J X] {a : R} (ha : ∀ n, IsSMulRegular (X ⧸ J ^ n) (σ a))
    [Algebra.FormallyUnramified R (Localization.Away a ⊗[R] T)] (ψ₁ ψ₂ : T →+* X)
    (h₁ : ψ₁.comp (algebraMap R T) = σ) (h₂ : ψ₂.comp (algebraMap R T) = σ)
    (h : (Ideal.Quotient.mk J).comp ψ₁ = (Ideal.Quotient.mk J).comp ψ₂) : ψ₁ = ψ₂ := by
  let := σ.toAlgebra
  have ha' (n : ℕ) : IsSMulRegular (X ⧸ J ^ n) a := by
    have e (x : X ⧸ J ^ n) : σ a • x = a • x := algebraMap_smul X a x
    intro x y hxy
    refine ha n ?_
    simpa only [e] using hxy
  let ψ₁' : T →ₐ[R] X := { ψ₁ with commutes' := fun r ↦ RingHom.congr_fun h₁ r }
  let ψ₂' : T →ₐ[R] X := { ψ₂ with commutes' := fun r ↦ RingHom.congr_fun h₂ r }
  have := algHom_eq_of_isAdicComplete J ha' ψ₁' ψ₂' (AlgHom.ext fun t ↦ RingHom.congr_fun h t)
  exact RingHom.ext fun t ↦ AlgHom.congr_fun this t

end RingTheory.DepthTwo
