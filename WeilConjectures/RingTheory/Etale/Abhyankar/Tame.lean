/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.Abhyankar.Basic
public import WeilConjectures.Mathlib.RingTheory.Unramified.LocalRing
public import WeilConjectures.RingTheory.DiscreteValuationRing.AdjoinRoot
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The tame local computation in Abhyankar's lemma

Let `O` be a discrete valuation ring with uniformizer `π`, and `B` a finite `O`-algebra with
`π = u ϖᵉ` for a unit `u` of `B`, `e` invertible in `O` and `B ⧸ ϖ` formally unramified over
`O`. Let `O₂ = O[t]/(t^{em} - π)`. Then the integral closure of `O₂` in `O₂ ⊗[O] K` is finite
étale over `O₂`, where `K` is a localization of `B` inverting `π`
(`IsDiscreteValuationRing.Abhyankar.etale_integralClosure_of_eq_unit_mul_pow`).

The integral closure is the ring `D = B[Y, T]/(Yᵉ - u, Tᵐ - Yϖ)` (`Abhyankar.TameRing`), embedded
by `T ↦ t`, `Y ↦ tᵐ/ϖ`: its closed fibre `D/TD` is a quotient of `(B/ϖ)[Y]/(Yᵉ - u)`, hence
formally unramified, so that `D` is étale over `O₂`, and `D/TD` is reduced, so that `D` is
integrally closed in `O₂ ⊗[O] K`.
-/

@[expose] public section

open Polynomial TensorProduct

namespace IsDiscreteValuationRing.Abhyankar

variable {B : Type*} [CommRing B] (e m : ℕ) (u ϖ : B)

/-- The ring `B[Y]/(Yᵉ - u)`. -/
abbrev KummerRing := AdjoinRoot (X ^ e - C u)

/-- The ring `B[Y, T]/(Yᵉ - u, Tᵐ - Yϖ)`, presented as `(B[Y]/(Yᵉ - u))[T]/(Tᵐ - Yϖ)`. -/
abbrev TameRing :=
  AdjoinRoot (X ^ m - C (AdjoinRoot.root (X ^ e - C u) * algebraMap B (KummerRing e u) ϖ))

/-- The element `T` of `TameRing`. -/
noncomputable abbrev tameRoot : TameRing e m u ϖ := AdjoinRoot.root _

/-- The element `Y` of `TameRing`. -/
noncomputable abbrev kummerRoot : TameRing e m u ϖ :=
  algebraMap (KummerRing e u) _ (AdjoinRoot.root (X ^ e - C u))

theorem kummerRoot_pow : kummerRoot e m u ϖ ^ e = algebraMap B (TameRing e m u ϖ) u := by
  have h0 := AdjoinRoot.mk_self (f := X ^ e - C u)
  rw [← AdjoinRoot.aeval_eq, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h0
  rw [kummerRoot, ← map_pow, h0, ← IsScalarTower.algebraMap_apply]

theorem tameRoot_pow :
    tameRoot e m u ϖ ^ m = kummerRoot e m u ϖ * algebraMap B (TameRing e m u ϖ) ϖ := by
  have h0 := AdjoinRoot.mk_self
    (f := X ^ m - C (AdjoinRoot.root (X ^ e - C u) * algebraMap B (KummerRing e u) ϖ))
  rw [← AdjoinRoot.aeval_eq, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h0
  rw [tameRoot, h0, map_mul, ← IsScalarTower.algebraMap_apply]

theorem tameRoot_pow_mul :
    tameRoot e m u ϖ ^ (e * m) = algebraMap B (TameRing e m u ϖ) (u * ϖ ^ e) := by
  rw [pow_mul', tameRoot_pow, mul_pow, kummerRoot_pow, ← map_pow, ← map_mul]

theorem isUnit_kummerRoot (he : e ≠ 0) (hu : IsUnit u) : IsUnit (kummerRoot e m u ϖ) := by
  rw [← isUnit_pow_iff he, kummerRoot_pow]
  exact hu.map _

instance [NeZero e] : Module.Free B (KummerRing e u) :=
  .of_basis (AdjoinRoot.powerBasis' (monic_X_pow_sub_C u (NeZero.ne e))).basis

instance [NeZero e] : Module.Finite B (KummerRing e u) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C u (NeZero.ne e))).finite

instance [NeZero m] : Module.Free (KummerRing e u) (TameRing e m u ϖ) :=
  .of_basis (AdjoinRoot.powerBasis' (monic_X_pow_sub_C _ (NeZero.ne m))).basis

instance [NeZero m] : Module.Finite (KummerRing e u) (TameRing e m u ϖ) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C _ (NeZero.ne m))).finite

instance [NeZero e] [NeZero m] : Module.Free B (TameRing e m u ϖ) :=
  Module.Free.trans (S := KummerRing e u)

instance [NeZero e] [NeZero m] : Module.Finite B (TameRing e m u ϖ) :=
  .trans (KummerRing e u) _

/-- The closed fibre `D/TD` of the tame ring is formally unramified over `O` when `B ⧸ ϖ` is. -/
theorem formallyUnramified_quotient_tameRoot {O : Type*} [CommRing O] [Algebra O B] [NeZero e]
    (he : IsUnit (e : B)) (hu : IsUnit u) (hm : m ≠ 0)
    [Algebra.FormallyUnramified O (B ⧸ Ideal.span {ϖ})] :
    Algebra.FormallyUnramified O (TameRing e m u ϖ ⧸ Ideal.span {tameRoot e m u ϖ}) := by
  let D := TameRing e m u ϖ
  let J := Ideal.span {tameRoot e m u ϖ}
  have hϖJ : Ideal.span {ϖ} ≤ J.comap (algebraMap B D) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    obtain ⟨v, hv⟩ := isUnit_kummerRoot e m u ϖ (NeZero.ne e) hu
    have hϖ : algebraMap B D ϖ = ↑v⁻¹ * tameRoot e m u ϖ ^ m := by
      rw [tameRoot_pow, ← hv, Units.inv_mul_cancel_left]
    rw [hϖ]
    exact Ideal.mul_mem_left _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (Nat.pos_of_ne_zero hm))
  let _ : Algebra (B ⧸ Ideal.span {ϖ}) (D ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hϖJ
  have : IsScalarTower B (B ⧸ Ideal.span {ϖ}) (D ⧸ J) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower O (B ⧸ Ideal.span {ϖ}) (D ⧸ J) := .of_algebraMap_eq fun x ↦
    congrArg (Ideal.Quotient.mk J) (IsScalarTower.algebraMap_apply O B D x)
  have : Algebra.FormallyUnramified B (KummerRing e u) :=
    AdjoinRoot.formallyUnramified_X_pow_sub_C he hu
  have hsurj : Function.Surjective (Algebra.ofId (KummerRing e u) (D ⧸ J)) := by
    intro x
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, y, rfl⟩ := (AdjoinRoot.isAdjoinRoot _).exists_eq_algebraMap_add_root_mul d
    refine ⟨a, ?_⟩
    rw [Algebra.ofId_apply, map_add, AdjoinRoot.isAdjoinRoot_root_eq_root,
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)), add_zero]
    rfl
  have : Algebra.FormallyUnramified (KummerRing e u) (D ⧸ J) := .of_surjective _ hsurj
  have : Algebra.FormallyUnramified B (D ⧸ J) := .comp B (KummerRing e u) (D ⧸ J)
  have : Algebra.FormallyUnramified (B ⧸ Ideal.span {ϖ}) (D ⧸ J) := .of_restrictScalars B _ _
  exact .comp O (B ⧸ Ideal.span {ϖ}) (D ⧸ J)

omit [CommRing B] in
/-- Let `S` be an `O₂`-subalgebra of `O₂ ⊗[O] K` and `t ∈ O₂` with `tⁿ = π`. If every `1 ⊗ k`
lands in `S` after multiplication by a power of `π`, then every element of `O₂ ⊗[O] K` lands in
`S` after multiplication by a power of `t`. -/
theorem exists_pow_smul_mem_of_tmul {O O₂ K : Type*} [CommRing O] [CommRing O₂] [CommRing K]
    [Algebra O O₂] [Algebra O K] (S : Subalgebra O₂ (O₂ ⊗[O] K)) {t : O₂} {π : O} {n : ℕ}
    (ht : t ^ n = algebraMap O O₂ π) (hS : ∀ k : K, ∃ j : ℕ, (1 : O₂) ⊗ₜ[O] (π ^ j • k) ∈ S)
    (a : O₂ ⊗[O] K) : ∃ k : ℕ, t ^ k • a ∈ S := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x k =>
    obtain ⟨j, hj⟩ := hS k
    refine ⟨n * j, ?_⟩
    rw [pow_mul, ht, ← map_pow, algebraMap_smul, ← tmul_smul]
    have h := S.smul_mem hj x
    rwa [smul_tmul', smul_eq_mul, mul_one] at h
  | add x y hx hy =>
    obtain ⟨k₁, hk₁⟩ := hx
    obtain ⟨k₂, hk₂⟩ := hy
    refine ⟨k₁ + k₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [pow_add, mul_comm, ← smul_smul]
      exact S.smul_mem hk₁ _
    · rw [pow_add, ← smul_smul]
      exact S.smul_mem hk₂ _

set_option maxHeartbeats 1000000 in
-- the proof elaborates many algebra structures on tensor products and `AdjoinRoot`s
/-- **The tame local computation of Abhyankar's lemma.** Let `O` be a discrete valuation ring with
uniformizer `π`, `B` a finite `O`-algebra with `π = u ϖᵉ` for a unit `u` of `B`, `e` invertible
in `O` and `B ⧸ ϖ` formally unramified over `O`, and `K` a `B`-algebra into which `B` injects,
in which `π` is invertible and such that `K = B[1/π]`. Then for `O₂ = O[t]/(t^{em} - π)`, the
integral closure of `O₂` in `O₂ ⊗[O] K` is finite étale over `O₂`. -/
theorem etale_integralClosure_of_eq_unit_mul_pow {O K : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O B] [Module.Finite O B] [CommRing K]
    [Algebra O K] [Algebra B K] [IsScalarTower O B K] (hBK : Function.Injective (algebraMap B K))
    {π : O} (hπ : Irreducible π) (hπK : IsUnit (algebraMap O K π))
    (hspan : ∀ k : K, ∃ j : ℕ, π ^ j • k ∈ Set.range (algebraMap B K))
    {e m : ℕ} (he : IsUnit (e : O)) (hm : m ≠ 0) {u ϖ : B} (hu : IsUnit u)
    (hπu : algebraMap O B π = u * ϖ ^ e) [Algebra.FormallyUnramified O (B ⧸ Ideal.span {ϖ})]
    (O₂ : Type*) [CommRing O₂] [Algebra O O₂] (hO₂ : IsAdjoinRoot O₂ (X ^ (e * m) - C π)) :
    Algebra.Etale O₂ (integralClosure O₂ (O₂ ⊗[O] K)) ∧
      Module.Finite O₂ (integralClosure O₂ (O₂ ⊗[O] K)) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at he
    exact not_isUnit_zero he
  have : NeZero e := ⟨he0⟩
  have : NeZero m := ⟨hm⟩
  have hn : e * m ≠ 0 := mul_ne_zero he0 hm
  have : IsDomain O₂ := hO₂.isDomain_of_X_pow_sub_C hπ hn
  have : IsLocalRing O₂ := hO₂.isLocalRing_of_X_pow_sub_C hπ hn
  have : IsDiscreteValuationRing O₂ := hO₂.isDiscreteValuationRing_of_X_pow_sub_C hπ hn
  have hmax := hO₂.maximalIdeal_eq_span_root hπ hn
  have hirr : Irreducible hO₂.root := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, hmax]
  -- the `O₂`-algebra structure on `D`
  let D := TameRing e m u ϖ
  have hTπ : (X ^ (e * m) - C π).eval₂ (algebraMap O D) (tameRoot e m u ϖ) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, tameRoot_pow_mul, ← hπu,
      ← IsScalarTower.algebraMap_apply, sub_self]
  let _ : Algebra O₂ D := (hO₂.lift (algebraMap O D) _ hTπ).toAlgebra
  have : IsScalarTower O O₂ D := .of_algebraMap_eq fun x ↦ (hO₂.lift_algebraMap hTπ x).symm
  have hroot : algebraMap O₂ D hO₂.root = tameRoot e m u ϖ := hO₂.lift_root hTπ
  have : Module.Finite O D := .trans B D
  have : Module.Finite O₂ D := .of_restrictScalars_finite O O₂ D
  -- the embedding `φ : D → O₂ ⊗[O] K`
  have hϖK : IsUnit (algebraMap B K ϖ) := by
    rw [IsScalarTower.algebraMap_apply O B K, hπu, map_mul, map_pow] at hπK
    exact (isUnit_pow_iff he0).mp (isUnit_of_mul_isUnit_right hπK)
  let i₀ : B →+* O₂ ⊗[O] K :=
    (Algebra.TensorProduct.includeRight : K →ₐ[O] O₂ ⊗[O] K).toRingHom.comp (algebraMap B K)
  have hi₀ (b : B) : i₀ b = 1 ⊗ₜ algebraMap B K b := rfl
  let y₀ : O₂ ⊗[O] K := (hO₂.root ^ m) ⊗ₜ (↑hϖK.unit⁻¹ : K)
  have hy₀ : (X ^ e - C u).eval₂ i₀ y₀ = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, hi₀, Algebra.TensorProduct.tmul_pow,
      ← pow_mul, mul_comm m e,
      hO₂.root_pow_eq, Algebra.algebraMap_eq_smul_one (A := O₂) π, smul_tmul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply O B K, hπu, map_mul, map_pow, mul_assoc, ← mul_pow,
      IsUnit.mul_val_inv, one_pow, mul_one]
  let ψ₁ : KummerRing e u →+* O₂ ⊗[O] K := AdjoinRoot.lift i₀ y₀ hy₀
  have hψB (b : B) : ψ₁ (algebraMap B (KummerRing e u) b) = i₀ b := AdjoinRoot.lift_of hy₀
  have hT₀ : (X ^ m - C (AdjoinRoot.root (X ^ e - C u) *
      algebraMap B (KummerRing e u) ϖ)).eval₂ ψ₁ (hO₂.root ⊗ₜ 1) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, map_mul, AdjoinRoot.lift_root, hψB, hi₀,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_pow, one_pow, mul_one,
      IsUnit.val_inv_mul]
  let φ₀ : D →+* O₂ ⊗[O] K := AdjoinRoot.lift ψ₁ _ hT₀
  have hφK (z : KummerRing e u) : φ₀ (algebraMap (KummerRing e u) D z) = ψ₁ z :=
    AdjoinRoot.lift_of hT₀
  have hφB (b : B) : φ₀ (algebraMap B D b) = 1 ⊗ₜ algebraMap B K b := by
    rw [IsScalarTower.algebraMap_apply B (KummerRing e u) D, hφK, hψB, hi₀]
  have hφT : φ₀ (tameRoot e m u ϖ) = hO₂.root ⊗ₜ 1 := AdjoinRoot.lift_root hT₀
  have hK₂π : (X ^ (e * m) - C π).eval₂ (algebraMap O (O₂ ⊗[O] K)) (hO₂.root ⊗ₜ 1) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, Algebra.TensorProduct.tmul_pow, one_pow,
      hO₂.root_pow_eq]
    rfl
  have hφ₀ (a : O₂) : φ₀ (algebraMap O₂ D a) = algebraMap O₂ (O₂ ⊗[O] K) a := by
    rw [← RingHom.comp_apply, hO₂.apply_eq_lift hK₂π (φ₀.comp (algebraMap O₂ D)) (fun x ↦ ?_)
      (by rw [RingHom.comp_apply, hroot, hφT]), ← hO₂.apply_eq_lift hK₂π
        (algebraMap O₂ (O₂ ⊗[O] K)) (fun x ↦ (IsScalarTower.algebraMap_apply _ _ _ x).symm) rfl]
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O B D,
      hφB, ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  let φ : D →ₐ[O₂] O₂ ⊗[O] K := { φ₀ with commutes' := hφ₀ }
  have hφφ₀ (d : D) : φ d = φ₀ d := rfl
  have hφ : Function.Injective φ := by
    have hf : aeval ((1 : K) ⊗ₜ[B] tameRoot e m u ϖ) (X ^ (e * m) - C π) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero, Algebra.TensorProduct.tmul_pow,
        one_pow, tameRoot_pow_mul, ← hπu, Algebra.TensorProduct.algebraMap_apply,
        IsScalarTower.algebraMap_apply O B K, Algebra.algebraMap_eq_smul_one (A := K),
        smul_tmul, Algebra.algebraMap_eq_smul_one (A := D)]
    let ψ : O₂ ⊗[O] K →ₐ[O] K ⊗[B] D := Algebra.TensorProduct.lift (hO₂.liftHom _ hf)
      Algebra.TensorProduct.includeLeft fun _ _ ↦ .all _ _
    have hψφ : (ψ : O₂ ⊗[O] K →+* K ⊗[B] D).comp φ₀ =
        (Algebra.TensorProduct.includeRight : D →ₐ[B] K ⊗[B] D) := by
      refine AdjoinRoot.ringHom_ext (AdjoinRoot.ringHom_ext (RingHom.ext fun b ↦ ?_) ?_) ?_
      · simp only [RingHom.comp_apply, RingHom.coe_coe]
        refine (congrArg ψ (hφB b)).trans ?_
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul,
          Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.algebraMap_eq_smul_one (A := K) b, smul_tmul,
          ← Algebra.algebraMap_eq_smul_one (A := D) b]
        rfl
      · simp only [RingHom.comp_apply, RingHom.coe_coe]
        refine (congrArg ψ (hφK _)).trans ?_
        rw [AdjoinRoot.lift_root, Algebra.TensorProduct.lift_tmul, map_pow,
          IsAdjoinRoot.liftHom_root, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.tmul_pow, one_pow, tameRoot_pow,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm (kummerRoot e m u ϖ),
          ← Algebra.smul_def, ← smul_tmul, Algebra.smul_def, IsUnit.mul_val_inv,
          Algebra.TensorProduct.includeRight_apply]
        rfl
      · simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [AdjoinRoot.lift_root, Algebra.TensorProduct.lift_tmul, IsAdjoinRoot.liftHom_root,
          map_one, mul_one, Algebra.TensorProduct.includeRight_apply]
    intro x y hxy
    refine Algebra.TensorProduct.includeRight_injective (A := K) hBK ?_
    calc Algebra.TensorProduct.includeRight x = ((ψ : O₂ ⊗[O] K →+* K ⊗[B] D).comp φ₀) x :=
          (RingHom.congr_fun hψφ x).symm
      _ = ((ψ : O₂ ⊗[O] K →+* K ⊗[B] D).comp φ₀) y := congrArg ψ hxy
      _ = Algebra.TensorProduct.includeRight y := RingHom.congr_fun hψφ y
  have hspan₂ := exists_pow_smul_mem_of_tmul φ.range (hO₂.root_pow_eq) fun k ↦ by
    obtain ⟨j, b, hb⟩ := hspan k
    refine ⟨j, φ.mem_range.mpr ⟨algebraMap B D b, ?_⟩⟩
    rw [hφφ₀, hφB, hb]
  have hπK₂ : IsUnit (algebraMap O (O₂ ⊗[O] K) π) := by
    rw [← (Algebra.TensorProduct.includeRight : K →ₐ[O] O₂ ⊗[O] K).commutes]
    exact hπK.map _
  have hrootK : IsUnit (algebraMap O₂ (O₂ ⊗[O] K) hO₂.root) := by
    rw [← isUnit_pow_iff hn, ← map_pow, hO₂.root_pow_eq, ← IsScalarTower.algebraMap_apply]
    exact hπK₂
  have hunit (a : O₂) (ha : a ≠ 0) : IsUnit (algebraMap O₂ (O₂ ⊗[O] K) a) := by
    obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hirr
    rw [map_mul, map_pow]
    exact (v.isUnit.map _).mul (hrootK.pow _)
  -- étaleness of `D`
  have : Module.IsTorsionFree O₂ D := .of_smul_eq_zero fun r d hrd ↦ by
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr (hφ ?_)
    have h0 := congrArg φ hrd
    rw [map_smul, map_zero, Algebra.smul_def] at h0
    rw [map_zero]
    exact (hunit r hr).mul_right_eq_zero.mp h0
  have : Algebra.FormallyUnramified O₂
      (D ⧸ (IsLocalRing.maximalIdeal O₂).map (algebraMap O₂ D)) := by
    rw [hmax, Ideal.map_span, Set.image_singleton, hroot]
    have := formallyUnramified_quotient_tameRoot e m u ϖ (O := O)
      ((map_natCast (algebraMap O B) e) ▸ he.map (algebraMap O B)) hu hm
    exact .of_restrictScalars O _ _
  have : Algebra.Etale O₂ D := Algebra.Etale.of_formallyUnramified_quotient_map_maximalIdeal
  -- `D` is the integral closure
  have : IsReduced (D ⧸ Ideal.span {algebraMap O₂ D hO₂.root}) := by
    have := Algebra.FormallyUnramified.isReduced_quotient_map_maximalIdeal (R := O₂) (S := D)
    rwa [hmax, Ideal.map_span, Set.image_singleton] at this
  have hrange := φ.range_eq_integralClosure_of_isReduced hφ hO₂.root hrootK hspan₂
  let E : D ≃ₐ[O₂] integralClosure O₂ (O₂ ⊗[O] K) :=
    (AlgEquiv.ofInjective φ hφ).trans (Subalgebra.equivOfEq _ _ hrange)
  exact ⟨.of_equiv E, .equiv E.toLinearEquiv⟩

end IsDiscreteValuationRing.Abhyankar
