/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Lift
public import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# Lifting points along the quotients of an adically complete algebra

This is the variant of `RingTheory.DepthTwo.exists_liftAlgHom` in which the tower `R / Iⁿ` of
quotients of the base ring is replaced by the tower `C / Jⁿ` of quotients of an `O`-algebra `C`.
Let `a, b ∈ O` be such that `(a, b)` is a regular pair on every `C / Jⁿ`, and let `T` be an
`O`-algebra such that `O_a ⊗ T` and `O_b ⊗ T` are formally étale over `O`. Then every
`O`-algebra map `T → C / J` lifts uniquely to `T → C / Jⁿ` for all `n ≥ 1`
(`RingTheory.DepthTwo.existsUnique_liftQuot`), hence to `T → C` if `C` is `J`-adically complete
(`RingTheory.DepthTwo.exists_liftAlgHom_of_isAdicComplete`). The ring homomorphism version
`RingTheory.DepthTwo.exists_ringHom_lift_of_isAdicComplete` allows the structure map `O → C` to
be an arbitrary ring homomorphism.
-/

@[expose] public section

open TensorProduct

namespace RingTheory.DepthTwo

variable {O : Type*} [CommRing O] {C : Type*} [CommRing C] [Algebra O C] (J : Ideal C)
  (a b : O) {T : Type*} [CommRing T] [Algebra O T]

/-- The kernel of `C / J^(m+1) → C / J^m` has square zero for `m ≥ 1`. -/
lemma ker_factorₐ_pow_succ_sq' {m : ℕ} (hm : 1 ≤ m) :
    RingHom.ker (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (I := J) m.le_succ)) ^ 2 =
      ⊥ :=
  ker_factorₐ_pow_succ_sq J hm

/-- The reduction map `O_c ⊗ C / J^(m+1) → O_c ⊗ C / J^m`. -/
noncomputable abbrev reduceAwayQuot (c : O) (m : ℕ) :
    Localization.Away c ⊗[O] (C ⧸ J ^ (m + 1)) →ₐ[O] Localization.Away c ⊗[O] (C ⧸ J ^ m) :=
  Algebra.TensorProduct.map (AlgHom.id O _)
    (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (I := J) m.le_succ))

lemma surjective_reduceAwayQuot (c : O) (m : ℕ) : Function.Surjective (reduceAwayQuot J c m) :=
  LinearMap.lTensor_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := J) m.le_succ))

lemma isNilpotent_ker_reduceAwayQuot (c : O) {m : ℕ} (hm : 1 ≤ m) :
    IsNilpotent (RingHom.ker (reduceAwayQuot J c m)) :=
  isNilpotent_ker_map_id _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := J) m.le_succ))
    (ker_factorₐ_pow_succ_sq' J hm)

/-- One step of the lifting: a map `T → C / J^m` lifts to `T → C / J^(m+1)`, uniquely. -/
lemma existsUnique_liftQuot_succ (hJ : ∀ n, IsRegularPair a b (C ⧸ J ^ n))
    [Algebra.FormallyEtale O (Localization.Away a ⊗[O] T)]
    [Algebra.FormallyEtale O (Localization.Away b ⊗[O] T)]
    {m : ℕ} (hm : 1 ≤ m) (f : T →ₐ[O] C ⧸ J ^ m) :
    ∃! F : T →ₐ[O] C ⧸ J ^ (m + 1),
      (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (I := J) m.le_succ)).comp F = f := by
  set fac := Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (I := J) m.le_succ)
  -- the lifts on `D(a)` and `D(b)`
  have hlift (c : O) [Algebra.FormallyEtale O (Localization.Away c ⊗[O] T)] :
      ∃ G : Localization.Away c ⊗[O] T →ₐ[O] Localization.Away c ⊗[O] (C ⧸ J ^ (m + 1)),
        (reduceAwayQuot J c m).comp G = Algebra.TensorProduct.map (AlgHom.id O _) f :=
    ⟨Algebra.FormallySmooth.liftOfSurjective _ _ (surjective_reduceAwayQuot J c m)
      (isNilpotent_ker_reduceAwayQuot J c hm),
      Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _⟩
  obtain ⟨Ga, hGa⟩ := hlift a
  obtain ⟨Gb, hGb⟩ := hlift b
  let iRa : T →ₐ[O] Localization.Away a ⊗[O] T := Algebra.TensorProduct.includeRight
  let iRb : T →ₐ[O] Localization.Away b ⊗[O] T := Algebra.TensorProduct.includeRight
  let ρa := awayLift (R := O) a (isUnit_algebraMap_away_mul_left a b)
  let ρb := awayLift (R := O) b (isUnit_algebraMap_away_mul_right a b)
  have hcompat : (Algebra.TensorProduct.map ρa (AlgHom.id O (C ⧸ J ^ (m + 1)))).comp
      (Ga.comp iRa) = (Algebra.TensorProduct.map ρb (AlgHom.id O _)).comp (Gb.comp iRb) := by
    refine algHom_ext_of_formallyUnramified (c := a)
      (isUnit_algebraMap_tensor (isUnit_algebraMap_away_mul_left a b) _)
      (reduceAwayQuot J (a * b) m) (isNilpotent_ker_reduceAwayQuot J _ hm) _ _ ?_
    have e1 : (reduceAwayQuot J (a * b) m).comp
        (Algebra.TensorProduct.map ρa (AlgHom.id O _)) =
        (Algebra.TensorProduct.map ρa (AlgHom.id O _)).comp (reduceAwayQuot J a m) :=
      Algebra.TensorProduct.ext' fun x y ↦ by simp
    have e2 : (reduceAwayQuot J (a * b) m).comp
        (Algebra.TensorProduct.map ρb (AlgHom.id O _)) =
        (Algebra.TensorProduct.map ρb (AlgHom.id O _)).comp (reduceAwayQuot J b m) :=
      Algebra.TensorProduct.ext' fun x y ↦ by simp
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
    calc (Algebra.TensorProduct.includeRight : _ →ₐ[O] Localization.Away a ⊗[O] _) (fac (F t))
        = reduceAwayQuot J a m (Algebra.TensorProduct.includeRight (F t)) := by simp [fac]
      _ = reduceAwayQuot J a m (Ga (iRa t)) := by
        rw [← AlgHom.comp_apply _ F, hF]
        rfl
      _ = Algebra.TensorProduct.includeRight (f t) := by
        rw [← AlgHom.comp_apply, hGa]
        simp [iRa]
  -- uniqueness
  have huniq (F₁ F₂ : T →ₐ[O] C ⧸ J ^ (m + 1)) (h₁ : fac.comp F₁ = f) (h₂ : fac.comp F₂ = f) :
      F₁ = F₂ := by
    have hinj := injective_includeRight_of_isSMulRegular (hJ (m + 1)).1
    have : (Algebra.TensorProduct.includeRight : _ →ₐ[O] Localization.Away a ⊗[O] _).comp F₁ =
        Algebra.TensorProduct.includeRight.comp F₂ := by
      refine algHom_ext_of_formallyUnramified (c := a)
        (isUnit_algebraMap_tensor (IsLocalization.Away.algebraMap_isUnit a) _)
        (reduceAwayQuot J a m) (isNilpotent_ker_reduceAwayQuot J a hm) _ _ ?_
      ext t
      have e1 := AlgHom.congr_fun h₁ t
      have e2 := AlgHom.congr_fun h₂ t
      simp only [AlgHom.comp_apply] at e1 e2
      simp [fac, e1, e2]
    ext t
    exact hinj (AlgHom.congr_fun this t)
  exact ⟨F, hFf, fun F' hF' ↦ huniq _ _ hF' hFf⟩

/-- A map `T → C / J` lifts uniquely to `T → C / J^m` for every `m ≥ 1`. -/
lemma existsUnique_liftQuot (hJ : ∀ n, IsRegularPair a b (C ⧸ J ^ n))
    [Algebra.FormallyEtale O (Localization.Away a ⊗[O] T)]
    [Algebra.FormallyEtale O (Localization.Away b ⊗[O] T)]
    (φ : T →ₐ[O] C ⧸ J) {m : ℕ} (hm : 1 ≤ m) :
    ∃! F : T →ₐ[O] C ⧸ J ^ m, (Ideal.Quotient.factorₐ O (Ideal.pow_le_self (by omega))).comp F
      = φ := by
  induction m, hm using Nat.le_induction with
  | base =>
    let e := Ideal.quotientEquivAlgOfEq O (pow_one J).symm
    have hfe : (Ideal.Quotient.factorₐ O (Ideal.pow_le_self one_ne_zero)).comp e.toAlgHom =
        AlgHom.id O (C ⧸ J) := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun _ ↦ rfl)
    have hef : e.toAlgHom.comp (Ideal.Quotient.factorₐ O (Ideal.pow_le_self one_ne_zero)) =
        AlgHom.id O (C ⧸ J ^ 1) := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun _ ↦ rfl)
    refine ⟨e.toAlgHom.comp φ, ?_, fun F hF ↦ ?_⟩
    · beta_reduce
      rw [← AlgHom.comp_assoc, hfe, AlgHom.id_comp]
    · beta_reduce at hF
      rw [← hF, ← AlgHom.comp_assoc, hef, AlgHom.id_comp]
  | succ m hm ih =>
    obtain ⟨f, hf, hfu⟩ := ih
    obtain ⟨F, hF, hFu⟩ := existsUnique_liftQuot_succ J a b hJ hm f
    have hcomp : (Ideal.Quotient.factorₐ O (Ideal.pow_le_self (by omega))).comp
        (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (I := J) m.le_succ)) =
        Ideal.Quotient.factorₐ O (Ideal.pow_le_self (n := m + 1) (by omega)) :=
      Ideal.Quotient.factorₐ_comp _ _ _
    refine ⟨F, ?_, fun F' hF' ↦ hFu F' ?_⟩
    · beta_reduce
      rw [← hcomp, AlgHom.comp_assoc, hF, hf]
    · beta_reduce at hF' ⊢
      refine hfu _ ?_
      beta_reduce
      rw [← AlgHom.comp_assoc, hcomp, hF']

/-- **Lifting points to an adically complete algebra.** If `(a, b)` is a regular pair on all
`C / Jⁿ`, `C` is `J`-adically complete and `O_a ⊗ T`, `O_b ⊗ T` are formally étale over `O`, then
every `O`-algebra map `T → C / J` lifts to an `O`-algebra map `T → C`. -/
theorem exists_liftAlgHom_of_isAdicComplete [IsAdicComplete J C]
    (hJ : ∀ n, IsRegularPair a b (C ⧸ J ^ n))
    [Algebra.FormallyEtale O (Localization.Away a ⊗[O] T)]
    [Algebra.FormallyEtale O (Localization.Away b ⊗[O] T)]
    (φ : T →ₐ[O] C ⧸ J) :
    ∃ ψ : T →ₐ[O] C, (Ideal.Quotient.mkₐ O J).comp ψ = φ := by
  choose L hL hLu using fun n : ℕ ↦ existsUnique_liftQuot J a b hJ φ (m := n + 1) (by omega)
  let f (n : ℕ) : T →ₐ[O] C ⧸ J ^ n :=
    (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (I := J) n.le_succ)).comp (L n)
  have hf {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    have : (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (I := J) (by omega : m + 1 ≤ n + 1))
        ).comp (L n) = L m := by
      refine hLu m _ ?_
      beta_reduce
      rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
      exact hL n
    simp only [f, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
    rw [← this, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  refine ⟨IsAdicComplete.liftAlgHom J f hf, ?_⟩
  ext t
  have h1 := IsAdicComplete.mk_liftAlgHom J f hf 1 t
  have h2 := AlgHom.congr_fun (hL 1) t
  simp only [f, AlgHom.comp_apply] at h1 h2 ⊢
  have h3 := AlgHom.congr_fun (Ideal.Quotient.factorₐ_comp O
    (Ideal.pow_le_pow_right (I := J) (by norm_num : 1 ≤ 1 + 1))
    (Ideal.pow_le_self (n := 1) one_ne_zero)) (L 1 t)
  rw [AlgHom.comp_apply] at h3
  rw [← h2, ← h3, ← h1]
  rfl

section RingHom

variable {O C T : Type*} [CommRing O] [CommRing C] [CommRing T] [Algebra O T]

/-- **Lifting points to an adically complete ring**, ring homomorphism version: here the
structure map `ι : O → C` is an arbitrary ring homomorphism, and the regularity of `(a, b)` is
that of `(ι a, ι b)` on the `C`-modules `C / Jⁿ`. -/
theorem exists_ringHom_lift_of_isAdicComplete (ι : O →+* C) (J : Ideal C) [IsAdicComplete J C]
    (a b : O) (hJ : ∀ n, IsRegularPair (ι a) (ι b) (C ⧸ J ^ n))
    [Algebra.FormallyEtale O (Localization.Away a ⊗[O] T)]
    [Algebra.FormallyEtale O (Localization.Away b ⊗[O] T)]
    (φ : T →+* C ⧸ J) (hφ : φ.comp (algebraMap O T) = (Ideal.Quotient.mk J).comp ι) :
    ∃ ψ : T →+* C, ψ.comp (algebraMap O T) = ι ∧ (Ideal.Quotient.mk J).comp ψ = φ := by
  let _ : Algebra O C := ι.toAlgebra
  have hJ' (n : ℕ) : IsRegularPair a b (C ⧸ J ^ n) := by
    have hs (c : O) (x : C ⧸ J ^ n) : c • x = ι c • x := (algebraMap_smul C c x).symm
    obtain ⟨h1, h2, h3⟩ := hJ n
    refine ⟨fun x y h ↦ h1 (by simpa only [hs] using h),
      fun x y h ↦ h2 (by simpa only [hs] using h), fun m hm ↦ ?_⟩
    obtain ⟨y, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    rw [hs, hs] at hy
    obtain ⟨z, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (h3 m ((Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hy⟩))
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨z, hz.1, (hs a z).trans hz.2⟩
  let φ' : T →ₐ[O] C ⧸ J :=
    { φ with commutes' := fun x ↦ RingHom.congr_fun hφ x }
  obtain ⟨ψ, hψ⟩ := exists_liftAlgHom_of_isAdicComplete J a b hJ' φ'
  exact ⟨ψ.toRingHom, ψ.comp_algebraMap, RingHom.ext fun t ↦ AlgHom.congr_fun hψ t⟩

end RingHom

end RingTheory.DepthTwo
