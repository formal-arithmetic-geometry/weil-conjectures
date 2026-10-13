/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import WeilConjectures.RingTheory.Regular.Hartogs

/-!
# Lifting points of an algebra étale over a punctured neighbourhood to the adic completion

Let `R` be a ring, `I ⊆ R` an ideal and `a, b ∈ R` such that `[a, b]` is a regular pair on
every `R / Iⁿ`. Let `T` be an `R`-algebra such that `R_a ⊗ T` and `R_b ⊗ T` are formally étale
over `R`. Geometrically, `Spec T` is étale over the open `D(a) ∪ D(b)`, and `R / Iⁿ` has depth
two along `V(a, b)`, so that `R / Iⁿ` is the ring of functions on `D(a) ∪ D(b)` inside
`Spec (R / Iⁿ)`. Then every `R`-algebra map `T → R / I` lifts uniquely to `T → R / Iⁿ` for all
`n ≥ 1`, hence to `T → R^`, the `I`-adic completion
(`AdicCompletion.exists_liftAlgHom_of_formallyEtale`).

This is the step "`W₀` split implies `W` split" of the proof of [Stacks 0EY9], for the formal
neighbourhood of a section, without any finiteness of the ring of functions on the punctured
neighbourhood: the lifts are built level by level on `D(a)` and `D(b)` by formal étaleness and
glued along the regular pair (`RingTheory.Sequence.exists_eq_of_isLocalizedModule`).
-/

@[expose] public section

open scoped Pointwise

open TensorProduct

namespace RingTheory.DepthTwo

variable {R : Type*} [CommRing R]

/-- The elementwise form of "`(a, b)` is a regular pair on `M`" used for gluing along
`D(a) ∪ D(b)`: `a` and `b` are `M`-regular and `b` is regular on `M / aM`. -/
def IsRegularPair (a b : R) (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  IsSMulRegular M a ∧ IsSMulRegular M b ∧
    ∀ m : M, b • m ∈ a • (⊤ : Submodule R M) → m ∈ a • (⊤ : Submodule R M)

lemma isRegularPair_of_isWeaklyRegular {a b : R} {M : Type*} [AddCommGroup M] [Module R M]
    (h : Sequence.IsWeaklyRegular M [a, b]) (hb : IsSMulRegular M b) : IsRegularPair a b M :=
  ⟨(Sequence.IsWeaklyRegular.isSMulRegular_and_mem_smul_top h).1, hb,
    (Sequence.IsWeaklyRegular.isSMulRegular_and_mem_smul_top h).2⟩

/-- The canonical map `R_c → C` of `R`-algebras when `c` is invertible in `C`. -/
noncomputable def awayLift (c : R) {C : Type*} [CommRing C] [Algebra R C]
    (hc : IsUnit (algebraMap R C c)) : Localization.Away c →ₐ[R] C :=
  IsLocalization.liftAlgHom (f := Algebra.ofId R C) (M := Submonoid.powers c) (by
    rintro ⟨_, n, rfl⟩
    simpa using hc.pow n)

@[simp]
lemma awayLift_algebraMap (c : R) {C : Type*} [CommRing C] [Algebra R C]
    (hc : IsUnit (algebraMap R C c)) (r : R) :
    awayLift c hc (algebraMap R (Localization.Away c) r) = algebraMap R C r :=
  (awayLift c hc).commutes r

lemma isUnit_algebraMap_away_mul_left (a b : R) :
    IsUnit (algebraMap R (Localization.Away (a * b)) a) :=
  isUnit_of_mul_isUnit_left (y := algebraMap R (Localization.Away (a * b)) b)
    (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (a * b))

lemma isUnit_algebraMap_away_mul_right (a b : R) :
    IsUnit (algebraMap R (Localization.Away (a * b)) b) :=
  isUnit_of_mul_isUnit_right (x := algebraMap R (Localization.Away (a * b)) a)
    (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (a * b))

lemma isUnit_algebraMap_tensor {c : R} {A : Type*} [CommRing A] [Algebra R A]
    (hc : IsUnit (algebraMap R A c)) (M : Type*) [CommRing M] [Algebra R M] :
    IsUnit (algebraMap R (A ⊗[R] M) c) := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  exact hc.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] M)

/-- If `c` is `M`-regular, then `M → R_c ⊗ M` is injective. -/
lemma injective_includeRight_of_isSMulRegular {c : R} {M : Type*} [CommRing M] [Algebra R M]
    (hc : IsSMulRegular M c) :
    Function.Injective (Algebra.TensorProduct.includeRight : M →ₐ[R]
      Localization.Away c ⊗[R] M) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  have h : TensorProduct.mk R (Localization.Away c) M 1 m = TensorProduct.mk R _ M 1 0 := by
    simpa using hm
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c) h
  simp only [smul_zero, Submonoid.smul_def] at hn
  exact (hc.pow n) (by simpa using hn)

/-- If `g : C → D` is a surjection of `R`-algebras whose kernel has square zero, then so is its
base change `A ⊗ C → A ⊗ D`. -/
lemma isNilpotent_ker_map_id {A C D : Type*} [CommRing A] [Algebra R A] [CommRing C]
    [Algebra R C] [CommRing D] [Algebra R D] (g : C →ₐ[R] D) (hg : Function.Surjective g)
    (hsq : RingHom.ker g ^ 2 = ⊥) :
    IsNilpotent (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) g)) := by
  refine ⟨2, ?_⟩
  rw [Algebra.TensorProduct.lTensor_ker g hg, ← Ideal.map_pow, hsq, Ideal.map_bot]
  rfl

/-- The kernel of `R / I^(m+1) → R / I^m` has square zero for `m ≥ 1`. -/
lemma ker_factorₐ_pow_succ_sq (I : Ideal R) {m : ℕ} (hm : 1 ≤ m) :
    RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) m.le_succ)) ^ 2 =
      ⊥ := by
  have hker : RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) m.le_succ))
      = (I ^ m).map (Ideal.Quotient.mk (I ^ (m + 1))) := by
    rw [← Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (I := I) m.le_succ)]
    rfl
  rw [hker, ← Ideal.map_pow, eq_bot_iff, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  rw [← pow_mul] at hx
  exact Ideal.pow_le_pow_right (by omega) hx

variable (I : Ideal R) (a b : R) {T : Type*} [CommRing T] [Algebra R T]

/-- Two `R`-algebra maps `T → C`, with `c` invertible in `C` and `R_c ⊗ T` formally unramified
over `R`, which agree modulo a nilpotent ideal agree. -/
lemma algHom_ext_of_formallyUnramified {c : R} [Algebra.FormallyUnramified R
      (Localization.Away c ⊗[R] T)]
    {C D : Type*} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (hc : IsUnit (algebraMap R C c)) (q : C →ₐ[R] D) (hq : IsNilpotent (RingHom.ker q))
    (h₁ h₂ : T →ₐ[R] C) (h : q.comp h₁ = q.comp h₂) : h₁ = h₂ := by
  let H (h : T →ₐ[R] C) : Localization.Away c ⊗[R] T →ₐ[R] C :=
    Algebra.TensorProduct.lift (awayLift c hc) h fun _ _ ↦ Commute.all _ _
  have key : H h₁ = H h₂ := by
    refine Algebra.FormallyUnramified.lift_unique' q hq _ _ ?_
    refine Algebra.TensorProduct.ext' fun x t ↦ ?_
    simp only [H, AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul]
    rw [← AlgHom.comp_apply q h₁, ← AlgHom.comp_apply q h₂, h]
  ext t
  have := AlgHom.congr_fun key (1 ⊗ₜ t)
  simpa [H] using this

/-- The reduction map `R_c ⊗ R / I^(m+1) → R_c ⊗ R / I^m`. -/
noncomputable abbrev reduceAway (c : R) (m : ℕ) :
    Localization.Away c ⊗[R] (R ⧸ I ^ (m + 1)) →ₐ[R] Localization.Away c ⊗[R] (R ⧸ I ^ m) :=
  Algebra.TensorProduct.map (AlgHom.id R _)
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) m.le_succ))

lemma surjective_reduceAway (c : R) (m : ℕ) : Function.Surjective (reduceAway I c m) :=
  LinearMap.lTensor_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := I) m.le_succ))

lemma isNilpotent_ker_reduceAway (c : R) {m : ℕ} (hm : 1 ≤ m) :
    IsNilpotent (RingHom.ker (reduceAway I c m)) :=
  isNilpotent_ker_map_id _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := I) m.le_succ))
    (ker_factorₐ_pow_succ_sq I hm)

/-- Gluing `R`-algebra maps `T → R_a ⊗ M` and `T → R_b ⊗ M` which agree in `R_{ab} ⊗ M` to an
`R`-algebra map `T → M`, for `(a, b)` a regular pair on `M`. -/
lemma exists_algHom_of_isRegularPair {M : Type*} [CommRing M] [Algebra R M]
    (hM : IsRegularPair a b M)
    (ga : T →ₐ[R] Localization.Away a ⊗[R] M) (gb : T →ₐ[R] Localization.Away b ⊗[R] M)
    (h : (Algebra.TensorProduct.map (awayLift a (isUnit_algebraMap_away_mul_left a b))
        (AlgHom.id R M)).comp ga =
      (Algebra.TensorProduct.map (awayLift b (isUnit_algebraMap_away_mul_right a b))
        (AlgHom.id R M)).comp gb) :
    ∃ F : T →ₐ[R] M, Algebra.TensorProduct.includeRight.comp F = ga := by
  obtain ⟨hr, hs', hs⟩ := hM
  let iR : M →ₐ[R] Localization.Away a ⊗[R] M := Algebra.TensorProduct.includeRight
  have hinj : Function.Injective iR := injective_includeRight_of_isSMulRegular hr
  have hrange : ga.range ≤ iR.range := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨m, hm, -⟩ := Sequence.exists_eq_of_isLocalizedModule hr hs' hs
      (TensorProduct.mk R (Localization.Away a) M 1)
      (TensorProduct.mk R (Localization.Away b) M 1)
      (TensorProduct.mk R (Localization.Away (a * b)) M 1)
      ((awayLift a (isUnit_algebraMap_away_mul_left a b)).toLinearMap.rTensor M)
      ((awayLift b (isUnit_algebraMap_away_mul_right a b)).toLinearMap.rTensor M)
      (by ext m; simp) (by ext m; simp) (ga t) (gb t) (AlgHom.congr_fun h t)
    exact ⟨m, hm⟩
  refine ⟨(AlgEquiv.ofInjective iR hinj).symm.toAlgHom.comp (ga.codRestrict _ fun t ↦
    hrange ⟨t, rfl⟩), ?_⟩
  ext t
  simp only [AlgHom.comp_apply, AlgHom.coe_coe]
  exact congrArg Subtype.val ((AlgEquiv.ofInjective iR hinj).apply_symm_apply _)

/-- One step of the lifting: a map `T → R / I^m` lifts to `T → R / I^(m+1)`, uniquely. -/
lemma existsUnique_lift_succ (hRI : ∀ n, IsRegularPair a b (R ⧸ I ^ n))
    [Algebra.FormallyEtale R (Localization.Away a ⊗[R] T)]
    [Algebra.FormallyEtale R (Localization.Away b ⊗[R] T)]
    {m : ℕ} (hm : 1 ≤ m) (f : T →ₐ[R] R ⧸ I ^ m) :
    ∃! F : T →ₐ[R] R ⧸ I ^ (m + 1),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) m.le_succ)).comp F = f := by
  set fac := Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) m.le_succ)
  -- the lifts on `D(a)` and `D(b)`
  have hlift (c : R) [Algebra.FormallyEtale R (Localization.Away c ⊗[R] T)] :
      ∃ G : Localization.Away c ⊗[R] T →ₐ[R] Localization.Away c ⊗[R] (R ⧸ I ^ (m + 1)),
        (reduceAway I c m).comp G = Algebra.TensorProduct.map (AlgHom.id R _) f :=
    ⟨Algebra.FormallySmooth.liftOfSurjective _ _ (surjective_reduceAway I c m)
      (isNilpotent_ker_reduceAway I c hm), Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _⟩
  obtain ⟨Ga, hGa⟩ := hlift a
  obtain ⟨Gb, hGb⟩ := hlift b
  let iRa : T →ₐ[R] Localization.Away a ⊗[R] T := Algebra.TensorProduct.includeRight
  let iRb : T →ₐ[R] Localization.Away b ⊗[R] T := Algebra.TensorProduct.includeRight
  let ρa := awayLift (R := R) a (isUnit_algebraMap_away_mul_left a b)
  let ρb := awayLift (R := R) b (isUnit_algebraMap_away_mul_right a b)
  have hcompat : (Algebra.TensorProduct.map ρa (AlgHom.id R (R ⧸ I ^ (m + 1)))).comp
      (Ga.comp iRa) = (Algebra.TensorProduct.map ρb (AlgHom.id R _)).comp (Gb.comp iRb) := by
    refine algHom_ext_of_formallyUnramified (c := a)
      (isUnit_algebraMap_tensor (isUnit_algebraMap_away_mul_left a b) _)
      (reduceAway I (a * b) m) (isNilpotent_ker_reduceAway I _ hm) _ _ ?_
    have e1 : (reduceAway I (a * b) m).comp (Algebra.TensorProduct.map ρa (AlgHom.id R _)) =
        (Algebra.TensorProduct.map ρa (AlgHom.id R _)).comp (reduceAway I a m) := by
      exact Algebra.TensorProduct.ext' fun x y ↦ by simp
    have e2 : (reduceAway I (a * b) m).comp (Algebra.TensorProduct.map ρb (AlgHom.id R _)) =
        (Algebra.TensorProduct.map ρb (AlgHom.id R _)).comp (reduceAway I b m) := by
      exact Algebra.TensorProduct.ext' fun x y ↦ by simp
    ext t
    have h1 := AlgHom.congr_fun e1 (Ga (iRa t))
    have h2 := AlgHom.congr_fun e2 (Gb (iRb t))
    have h3 := AlgHom.congr_fun hGa (iRa t)
    have h4 := AlgHom.congr_fun hGb (iRb t)
    simp only [AlgHom.comp_apply] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4]
    simp [iRa, iRb]
  obtain ⟨F, hF⟩ := exists_algHom_of_isRegularPair a b (hRI (m + 1)) _ _ hcompat
  have hFf : fac.comp F = f := by
    have hinj := injective_includeRight_of_isSMulRegular (hRI m).1
    ext t
    apply hinj
    calc (Algebra.TensorProduct.includeRight : _ →ₐ[R] Localization.Away a ⊗[R] _) (fac (F t))
        = reduceAway I a m (Algebra.TensorProduct.includeRight (F t)) := by simp [fac]
      _ = reduceAway I a m (Ga (iRa t)) := by rw [← AlgHom.comp_apply _ F, hF]; rfl
      _ = Algebra.TensorProduct.includeRight (f t) := by
        rw [← AlgHom.comp_apply, hGa]; simp [iRa]
  -- uniqueness
  have huniq (F₁ F₂ : T →ₐ[R] R ⧸ I ^ (m + 1)) (h₁ : fac.comp F₁ = f) (h₂ : fac.comp F₂ = f) :
      F₁ = F₂ := by
    have hinj := injective_includeRight_of_isSMulRegular (hRI (m + 1)).1
    have : (Algebra.TensorProduct.includeRight : _ →ₐ[R] Localization.Away a ⊗[R] _).comp F₁ =
        Algebra.TensorProduct.includeRight.comp F₂ := by
      refine algHom_ext_of_formallyUnramified (c := a)
        (isUnit_algebraMap_tensor (IsLocalization.Away.algebraMap_isUnit a) _)
        (reduceAway I a m) (isNilpotent_ker_reduceAway I a hm) _ _ ?_
      ext t
      have e1 := AlgHom.congr_fun h₁ t
      have e2 := AlgHom.congr_fun h₂ t
      simp only [AlgHom.comp_apply] at e1 e2
      simp [fac, e1, e2]
    ext t
    exact hinj (AlgHom.congr_fun this t)
  exact ⟨F, hFf, fun F' hF' ↦ huniq _ _ hF' hFf⟩

/-- A map `T → R / I` lifts uniquely to `T → R / I^m` for every `m ≥ 1`. -/
lemma existsUnique_lift (hRI : ∀ n, IsRegularPair a b (R ⧸ I ^ n))
    [Algebra.FormallyEtale R (Localization.Away a ⊗[R] T)]
    [Algebra.FormallyEtale R (Localization.Away b ⊗[R] T)]
    (φ : T →ₐ[R] R ⧸ I) {m : ℕ} (hm : 1 ≤ m) :
    ∃! F : T →ₐ[R] R ⧸ I ^ m, (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (by omega))).comp F
      = φ := by
  induction m, hm using Nat.le_induction with
  | base =>
    let e := Ideal.quotientEquivAlgOfEq R (pow_one I).symm
    have hfe : (Ideal.Quotient.factorₐ R (Ideal.pow_le_self one_ne_zero)).comp e.toAlgHom =
        AlgHom.id R (R ⧸ I) := Ideal.Quotient.algHom_ext _ (by ext <;> rfl)
    have hef : e.toAlgHom.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_self one_ne_zero)) =
        AlgHom.id R (R ⧸ I ^ 1) := Ideal.Quotient.algHom_ext _ (by ext <;> rfl)
    refine ⟨e.toAlgHom.comp φ, by beta_reduce; rw [← AlgHom.comp_assoc, hfe, AlgHom.id_comp],
      fun F hF ↦ ?_⟩
    beta_reduce at hF
    rw [← hF, ← AlgHom.comp_assoc, hef, AlgHom.id_comp]
  | succ m hm ih =>
    obtain ⟨f, hf, hfu⟩ := ih
    obtain ⟨F, hF, hFu⟩ := existsUnique_lift_succ I a b hRI hm f
    have hcomp : (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (by omega))).comp
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) m.le_succ)) =
        Ideal.Quotient.factorₐ R (Ideal.pow_le_self (n := m + 1) (by omega)) :=
      Ideal.Quotient.factorₐ_comp _ _ _
    refine ⟨F, by beta_reduce; rw [← hcomp, AlgHom.comp_assoc, hF, hf], fun F' hF' ↦ hFu F' ?_⟩
    beta_reduce at hF' ⊢
    refine hfu _ ?_
    beta_reduce
    rw [← AlgHom.comp_assoc, hcomp, hF']

/-- **Lifting points to the adic completion.** If `(a, b)` is a regular pair on all `R / Iⁿ` and
`R_a ⊗ T`, `R_b ⊗ T` are formally étale over `R`, then every `R`-algebra map `T → R / I` lifts
to an `R`-algebra map `T → R^` to the `I`-adic completion. -/
theorem exists_liftAlgHom (hRI : ∀ n, IsRegularPair a b (R ⧸ I ^ n))
    [Algebra.FormallyEtale R (Localization.Away a ⊗[R] T)]
    [Algebra.FormallyEtale R (Localization.Away b ⊗[R] T)]
    (φ : T →ₐ[R] R ⧸ I) :
    ∃ ψ : T →ₐ[R] AdicCompletion I R, (AdicCompletion.evalOneₐ I).comp ψ = φ := by
  choose L hL hLu using fun n : ℕ ↦ existsUnique_lift I a b hRI φ (m := n + 1) (by omega)
  let f (n : ℕ) : T →ₐ[R] R ⧸ I ^ n :=
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) n.le_succ)).comp (L n)
  have hf {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    have : (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) (by omega : m + 1 ≤ n + 1))
        ).comp (L n) = L m := by
      refine hLu m _ ?_
      beta_reduce
      rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
      exact hL n
    simp only [f, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
    rw [← this, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  refine ⟨AdicCompletion.liftAlgHom I f hf, ?_⟩
  ext t
  rw [AlgHom.comp_apply, AdicCompletion.evalOneₐ_liftAlgHom]
  have := AlgHom.congr_fun (hL 1) t
  simp only [f, AlgHom.comp_apply] at this ⊢
  rw [← this, ← AlgHom.comp_apply, Ideal.Quotient.factorₐ_comp]

end RingTheory.DepthTwo
