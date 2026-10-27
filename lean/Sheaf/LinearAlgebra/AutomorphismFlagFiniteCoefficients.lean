/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Sheaf.FieldTheory.FieldTower

import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# An automorphism flag over a simultaneous finite coefficient field

Source: blueprint, `thm-zl-real-mixed-by-curves`, proof, paragraph 7,
dimension-zero Jordan filtration and its finite coefficient refinement
(blueprint: lem-zl-automorphism-flag-finite-coefficients).
-/

@[expose] public section

universe u v w

open TensorProduct

namespace LinearEquiv

private theorem flag_mem_iff
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {n : ℕ} (b : Module.Basis (Fin n) L M) (j : Fin (n + 1)) (x : M) :
    x ∈ b.flag j ↔ ∀ i : Fin n, j ≤ i.castSucc → b.repr x i = 0 := by
  rw [Module.Basis.flag, b.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  constructor
  · intro h i hi
    by_contra hn
    exact (not_lt_of_ge hi) (h i hn)
  · intro h i hi
    by_contra hn
    exact hi (h i (le_of_not_gt hn))

private theorem flag_basis_exists
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {n : ℕ} (b : Module.Basis (Fin n) L M) (j : Fin (n + 1)) :
    ∃ a : Module.Basis {i : Fin n // i.castSucc < j} L (b.flag j),
      ∀ i, (a i : M) = b i.val := by
  let v := fun i : {i : Fin n // i.castSucc < j} ↦ b i.val
  have hv : LinearIndependent L v := b.linearIndependent.comp _ Subtype.val_injective
  have hs : Submodule.span L (Set.range v) = b.flag j := by
    rw [Module.Basis.flag, Set.image_eq_range]
    rfl
  refine ⟨(Module.Basis.span hv).map (LinearEquiv.ofEq _ _ hs), ?_⟩
  intro i
  simp [Module.Basis.map_apply, v]

private theorem flag_finrank
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {n : ℕ} (b : Module.Basis (Fin n) L M) (j : Fin (n + 1)) :
    Module.finrank L (b.flag j) = j.val := by
  obtain ⟨a, _⟩ := flag_basis_exists b j
  rw [Module.finrank_eq_card_basis a]
  let e : {i : Fin n // i.castSucc < j} ≃ Fin j.val :=
    { toFun := fun i ↦ ⟨i.val.val, i.property⟩
      invFun := fun i ↦ ⟨⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩,
        i.isLt⟩
      left_inv := fun i ↦ rfl
      right_inv := fun i ↦ rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

private theorem triangular_preserves_flag
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {n : ℕ} (b : Module.Basis (Fin n) L M) (f : M →ₗ[L] M)
    (hf : (LinearMap.toMatrix b b f).IsUpperTriangular) (j : Fin (n + 1)) :
    b.flag j ≤ (b.flag j).comap f := by
  rw [b.flag_le_iff]
  intro i hi
  rw [Submodule.mem_comap, flag_mem_iff]
  intro k hk
  simpa only [LinearMap.toMatrix_apply] using hf (by
    change i < k
    change i.val < k.val
    change i.val < j.val at hi
    change j.val ≤ k.val at hk
    omega)

private theorem flag_coordinate
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {n : ℕ} (b : Module.Basis (Fin n) L M) (f : M →ₗ[L] M)
    (hf : (LinearMap.toMatrix b b f).IsUpperTriangular) (j : Fin n)
    (x : b.flag j.succ) :
    b.repr (f x) j = b.repr (f (b j)) j * b.repr (x : M) j := by
  classical
  have hs : b.repr (f x) j =
      ∑ i : Fin n, b.repr (x : M) i * b.repr (f (b i)) j := by
    rw [← LinearMap.toMatrix_mulVec_repr b b f (x : M)]
    simp [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, mul_comm]
  rw [hs, Finset.sum_eq_single j]
  · exact mul_comm _ _
  · intro i _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hz : b.repr (f (b i)) j = 0 := by
        simpa only [LinearMap.toMatrix_apply] using hf h
      rw [hz, mul_zero]
    · rw [(flag_mem_iff b j.succ x).mp x.property i (by
        change j.val + 1 ≤ i.val; exact h), zero_mul]
  · simp

private theorem invariant_restrict
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    (F : M ≃ₗ[L] M) (W : Submodule L M) [FiniteDimensional L W]
    (h : W ≤ W.comap F.toLinearMap) :
    ∃ r : W ≃ₗ[L] W, ∀ x : W, (r x : M) = F x ∧ (r.symm x : M) = F.symm x := by
  let f : W →ₗ[L] W := F.toLinearMap.restrict h
  have hinj : Function.Injective f := fun x y hxy ↦
    Subtype.ext (F.injective (congrArg Subtype.val hxy))
  let r := LinearEquiv.ofInjectiveEndo f hinj
  refine ⟨r, fun x ↦ ⟨rfl, ?_⟩⟩
  apply F.injective
  change (r (r.symm x) : M) = F (F.symm x)
  simp

private theorem flag_quotient
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {n : ℕ} (b : Module.Basis (Fin n) L M) (j : Fin n) :
    ∃ q : ((b.flag j.succ) ⧸
        ((b.flag j.castSucc).comap (b.flag j.succ).subtype)) ≃ₗ[L] L,
      ∀ x : b.flag j.succ,
        q (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
          b.repr (x : M) j := by
  let W := b.flag j.succ
  let U := (b.flag j.castSucc).comap W.subtype
  let f : W →ₗ[L] L := (b.coord j).comp W.subtype
  have hker : LinearMap.ker f = U := by
    ext x
    change b.repr (x : M) j = 0 ↔ (x : M) ∈ b.flag j.castSucc
    rw [flag_mem_iff]
    constructor
    · intro hx i hi
      rcases eq_or_lt_of_le hi with he | he
      · have he' : j = i := Fin.ext
          (show j.val = i.val from congrArg (fun z : Fin (n + 1) ↦ z.val) he)
        simpa [← he'] using hx
      · exact (flag_mem_iff b j.succ x).mp x.property i (by
          change j.val + 1 ≤ i.val; change j.val < i.val at he; omega)
    · exact fun h ↦ h j le_rfl
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨⟨a • b j, (b.flag j.succ).smul_mem a
      (b.self_mem_flag Fin.castSucc_lt_succ)⟩, ?_⟩
    simp [f, Module.Basis.coord_apply]
  let q := (Submodule.quotEquivOfEq U f.ker hker.symm).trans
    (f.quotKerEquivOfSurjective hsurj)
  exact ⟨q, fun x ↦ rfl⟩

private theorem flag_exact
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {n : ℕ} (b : Module.Basis (Fin n) L M) (j : Fin n) :
    Function.Injective (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j))) ∧
      Function.Exact (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j)))
        ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ ∧
      Function.Surjective ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ := by
  refine ⟨Submodule.inclusion_injective _, ?_, Submodule.mkQ_surjective _⟩
  rw [LinearMap.exact_iff]
  simp [Submodule.range_inclusion]

private theorem inverse_triangular
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    [FiniteDimensional L M] {n : ℕ} (b : Module.Basis (Fin n) L M)
    (F : M ≃ₗ[L] M) (hf : (LinearMap.toMatrix b b F.toLinearMap).IsUpperTriangular) :
    (LinearMap.toMatrix b b F.symm.toLinearMap).IsUpperTriangular := by
  intro i j hij
  obtain ⟨r, hr⟩ := invariant_restrict F (b.flag j.succ)
    (triangular_preserves_flag b F.toLinearMap hf j.succ)
  let x : b.flag j.succ := ⟨b j, b.self_mem_flag Fin.castSucc_lt_succ⟩
  have hx : F.symm (b j) ∈ b.flag j.succ := (hr x).2 ▸ (r.symm x).property
  simpa only [LinearMap.toMatrix_apply, LinearEquiv.coe_coe] using
    (flag_mem_iff b j.succ _).mp hx i (by
    change j.val + 1 ≤ i.val
    exact hij)

private theorem diagonal_ne_zero
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    [FiniteDimensional L M] {n : ℕ} (b : Module.Basis (Fin n) L M)
    (F : M ≃ₗ[L] M) (hf : (LinearMap.toMatrix b b F.toLinearMap).IsUpperTriangular)
    (j : Fin n) : b.repr (F (b j)) j ≠ 0 := by
  obtain ⟨r, hr⟩ := invariant_restrict F (b.flag j.succ)
    (triangular_preserves_flag b F.toLinearMap hf j.succ)
  let x : b.flag j.succ := ⟨b j, b.self_mem_flag Fin.castSucc_lt_succ⟩
  have h := flag_coordinate b F.toLinearMap hf j (r.symm x)
  change b.repr (F (r.symm x)) j = _ at h
  rw [(hr (r.symm x)).1.symm, r.apply_symm_apply] at h
  have h' : (1 : L) = b.repr (F (b j)) j * b.repr (r.symm x : M) j := by
    simpa [x] using h
  intro hz
  rw [hz, zero_mul] at h'
  exact one_ne_zero h'

private theorem triangular_flag_data
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    [FiniteDimensional L M] {n : ℕ} (b : Module.Basis (Fin n) L M)
    (F : M ≃ₗ[L] M) (hf : (LinearMap.toMatrix b b F.toLinearMap).IsUpperTriangular)
    (α : Fin n → Lˣ) (hα : ∀ j, (α j : L) = b.repr (F (b j)) j) :
        (∀ j : Fin (n + 1), Module.finrank L (b.flag j) = j.val) ∧
        (∀ j : Fin (n + 1),
          ∃ a : Module.Basis {i : Fin n // i.castSucc < j} L (b.flag j),
            ∀ i, (a i : M) = b i.val) ∧
        ∃ r : ∀ j : Fin (n + 1), (b.flag j) ≃ₗ[L] (b.flag j),
          (∀ (j : Fin (n + 1)) (x : b.flag j),
            (r j x : M) = F x ∧
            ((r j).symm x : M) = F.symm x) ∧
          ∃ q : ∀ j : Fin n, ((b.flag j.succ) ⧸
              ((b.flag j.castSucc).comap (b.flag j.succ).subtype)) ≃ₗ[L] L,
            ∃ g : ∀ j : Fin n, ((b.flag j.succ) ⧸
                ((b.flag j.castSucc).comap (b.flag j.succ).subtype)) ≃ₗ[L]
                ((b.flag j.succ) ⧸ ((b.flag j.castSucc).comap (b.flag j.succ).subtype)),
              (∀ (j : Fin n) (x : b.flag j.succ),
                q j (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  b.repr (x : M) j) ∧
              (∀ (j : Fin n) (x : b.flag j.succ),
                g j (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ (r j.succ x) ∧
                (g j).symm (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ ((r j.succ).symm x)) ∧
              (∀ (j : Fin n) x, q j (g j x) = (α j : L) * q j x) ∧
              (∀ j : Fin n,
                Function.Injective
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j))) ∧
                Function.Exact
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j)))
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ ∧
                Function.Surjective ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ) := by
  classical
  choose r hr using fun j ↦ invariant_restrict F (b.flag j)
    (triangular_preserves_flag b F.toLinearMap hf j)
  choose q hq using flag_quotient b
  let g := fun j ↦ ((q j).trans (LinearEquiv.smulOfUnit (α j))).trans (q j).symm
  have hg : ∀ (j : Fin n) x, q j (g j x) = (α j : L) * q j x := by
    intro j x
    simp [g, LinearEquiv.smulOfUnit, Units.smul_def, smul_eq_mul]
  have hgr : ∀ (j : Fin n) (x : b.flag j.succ),
      g j (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
        ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ (r j.succ x) := by
    intro j x
    apply (q j).injective
    rw [hg, hq, hq, (hr j.succ x).1, hα]
    simpa only [LinearEquiv.coe_coe] using
      (flag_coordinate b F.toLinearMap hf j x).symm
  refine ⟨flag_finrank b, flag_basis_exists b, r, hr, q, g, hq, ?_, hg, flag_exact b⟩
  intro j x
  refine ⟨hgr j x, ?_⟩
  apply (g j).injective
  rw [(g j).apply_symm_apply, hgr, (r j.succ).apply_symm_apply]

private theorem triangular_flag_data_tensor
    {L A M : Type*} [Field L] [Field A] [Algebra L A] [AddCommGroup M] [Module L M]
    [FiniteDimensional L M] {n : ℕ} (b : Module.Basis (Fin n) L M)
    (F : M ≃ₗ[L] M) (hf : (LinearMap.toMatrix b b F.toLinearMap).IsUpperTriangular)
    (α : Fin n → Lˣ) (hα : ∀ j, (α j : L) = b.repr (F (b j)) j) :
        (∀ j : Fin (n + 1), Module.finrank L (b.flag j) = j.val) ∧
        (∀ j : Fin (n + 1),
          ∃ a : Module.Basis {i : Fin n // i.castSucc < j} L (b.flag j),
            ∀ i, (a i : M) = b i.val) ∧
        ∃ r : ∀ j : Fin (n + 1), (b.flag j) ≃ₗ[L] (b.flag j),
          (∀ (j : Fin (n + 1)) (x : b.flag j),
            (r j x : M) = F x ∧
            ((r j).symm x : M) = F.symm x) ∧
          ∃ q : ∀ j : Fin n, ((b.flag j.succ) ⧸
              ((b.flag j.castSucc).comap (b.flag j.succ).subtype)) ≃ₗ[L] L,
            ∃ g : ∀ j : Fin n, ((b.flag j.succ) ⧸
                ((b.flag j.castSucc).comap (b.flag j.succ).subtype)) ≃ₗ[L]
                ((b.flag j.succ) ⧸ ((b.flag j.castSucc).comap (b.flag j.succ).subtype)),
              (∀ (j : Fin n) (x : b.flag j.succ),
                q j (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  b.repr (x : M) j) ∧
              (∀ (j : Fin n) (x : b.flag j.succ),
                g j (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ (r j.succ x) ∧
                (g j).symm (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ ((r j.succ).symm x)) ∧
              (∀ (j : Fin n) x, q j (g j x) = (α j : L) * q j x) ∧
              (∀ j : Fin n,
                Function.Injective
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j))) ∧
                Function.Exact
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j)))
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ ∧
                Function.Surjective ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ) ∧
              (∀ j : Fin n,
                Function.Injective (LinearMap.baseChange A
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j)))) ∧
                Function.Exact (LinearMap.baseChange A
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j))))
                  (LinearMap.baseChange A
                    ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ) ∧
                Function.Surjective (LinearMap.baseChange A
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ)) := by
  obtain ⟨hd, hab, r, hr, q, g, hq, hg, hs, he⟩ := triangular_flag_data b F hf α hα
  refine ⟨hd, hab, r, hr, q, g, hq, hg, hs, he, ?_⟩
  intro j
  simpa only [LinearMap.baseChange_eq_ltensor] using
    And.intro (Module.Flat.lTensor_preserves_injective_linearMap (M := A) _ (he j).1)
      (And.intro (Module.Flat.lTensor_exact A (he j).2.1)
        (LinearMap.lTensor_surjective A (he j).2.2))


private theorem scalar_extension_matrix
    {L A M : Type*} [Field L] [Field A] [Algebra L A]
    [AddCommGroup M] [Module L M] {n : ℕ}
    (b : Module.Basis (Fin n) L M) (f : M →ₗ[L] M) :
    LinearMap.toMatrix (b.baseChange A) (b.baseChange A) (f.baseChange A) =
      (LinearMap.toMatrix b b f).map (algebraMap L A) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Algebra.smul_def]

private theorem flag_base_change
    {L A M : Type*} [Field L] [Field A] [Algebra L A]
    [AddCommGroup M] [Module L M] {n : ℕ}
    (b : Module.Basis (Fin n) L M) (j : Fin (n + 1)) :
    (b.baseChange A).flag j = (b.flag j).baseChange A := by
  simp only [Module.Basis.flag, Submodule.baseChange_span, Set.image_image]
  congr 1
  ext x
  simp

private theorem basis_flag_map
    {L M N : Type*} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (b : Module.Basis (Fin n) L M)
    (e : M ≃ₗ[L] N) (j : Fin (n + 1)) :
    (b.map e).flag j = (b.flag j).map e.toLinearMap := by
  simp only [Module.Basis.flag, Submodule.map_span, Set.image_image]
  rfl

private theorem finite_basis_descent
    {L Ω M : Type*} [Field L] [Field Ω] [Algebra L Ω]
    [Algebra.IsAlgebraic L Ω] [AddCommGroup M] [Module L M]
    {n : ℕ} (c : Module.Basis (Fin n) L M)
    (a : Module.Basis (Fin n) Ω (Ω ⊗[L] M)) :
    ∃ E : IntermediateField L Ω, FiniteDimensional L E ∧
      ∃ b : Module.Basis (Fin n) E (E ⊗[L] M),
        (b.baseChange Ω).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M) = a := by
  classical
  have : FiniteDimensional L M := Module.Finite.of_basis c
  let S : Set Ω := Set.range (fun ij : Fin n × Fin n ↦ (c.baseChange Ω).repr (a ij.2) ij.1)
  let E := IntermediateField.adjoin L S
  have hfin : FiniteDimensional L E := IntermediateField.finiteDimensional_adjoin
    (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let v : Fin n → E ⊗[L] M := fun j ↦ (c.baseChange E).equivFun.symm
    (fun i ↦ ⟨(c.baseChange Ω).repr (a j) i,
      IntermediateField.subset_adjoin L S (Set.mem_range_self (i, j))⟩)
  let T := TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M
  let m : E ⊗[L] M →ₗ[E] Ω ⊗[L] M :=
    (T.restrictScalars E).toLinearMap.comp
      (TensorProduct.mk E Ω (E ⊗[L] M) 1)
  have hv : ∀ j, m (v j) = a j := by
    intro j
    apply (c.baseChange Ω).equivFun.injective
    ext i
    dsimp [v]
    rw [Module.Basis.equivFun_symm_apply]
    simp [m, T, IntermediateField.smul_def]
  have hli : LinearIndependent E v := LinearIndependent.of_comp m (by
    have h := a.linearIndependent.restrict_scalars' E
    simpa only [Function.comp_def, hv] using h)
  have hdim : Fintype.card (Fin n) = Module.finrank E (E ⊗[L] M) :=
    (Module.finrank_eq_card_basis (c.baseChange E)).symm
  have : FiniteDimensional E (E ⊗[L] M) := Module.Finite.of_basis (c.baseChange E)
  let b := basisOfLinearIndependentOfCardEqFinrank' v hli hdim
  have hb : ∀ j, b j = v j := fun j ↦ congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank' v hli hdim) j
  refine ⟨E, hfin, b, ?_⟩
  apply DFunLike.ext
  intro j
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb]
  change T (1 ⊗ₜ[E] v j) = a j
  have hm : ∀ x, T (1 ⊗ₜ[E] x) = m x := fun _ ↦ rfl
  rw [hm, hv]

private theorem tower_matrix
    {L Ω M : Type*} [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] {n : ℕ}
    (E : IntermediateField L Ω) (b : Module.Basis (Fin n) E (E ⊗[L] M))
    (f : M →ₗ[L] M) :
    LinearMap.toMatrix
      ((b.baseChange Ω).map (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M))
      ((b.baseChange Ω).map (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M))
      (f.baseChange Ω) =
      (LinearMap.toMatrix b b (f.baseChange E)).map (algebraMap E Ω) := by
  let T := TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M
  change LinearMap.toMatrix (b.baseChange Ω) (b.baseChange Ω)
    (T.symm.toLinearMap ∘ₗ (f.baseChange Ω) ∘ₗ T.toLinearMap) = _
  rw [← LinearMap.baseChange_baseChange, scalar_extension_matrix]

private theorem triangular_basis_of_card
    {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    [IsAlgClosed L] [FiniteDimensional L M] {n : ℕ}
    (c : Module.Basis (Fin n) L M) (f : M →ₗ[L] M) :
    ∃ b : Module.Basis (Fin n) L M,
      (LinearMap.toMatrix b b f).IsUpperTriangular := by
  have hdim : Module.finrank L M = n := by
    simpa using Module.finrank_eq_card_basis c
  obtain ⟨b, hb⟩ := Module.End.exists_basis_isUpperTriangular_toMatrix f
  revert b hb
  rw [hdim]
  exact fun b hb ↦ ⟨b, hb⟩

private theorem tower_equiv_matrix
    {L Ω M : Type*} [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] {n : ℕ}
    (E : IntermediateField L Ω) (b : Module.Basis (Fin n) E (E ⊗[L] M))
    (F : M ≃ₗ[L] M) :
    LinearMap.toMatrix
      ((b.baseChange Ω).map (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M))
      ((b.baseChange Ω).map (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M))
      (F.baseChange L Ω M M).toLinearMap =
      (LinearMap.toMatrix b b (F.baseChange L E M M).toLinearMap).map (algebraMap E Ω) := by
  exact tower_matrix E b F.toLinearMap

private theorem descended_triangular
    {L Ω M : Type*} [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] {n : ℕ}
    (E : IntermediateField L Ω) (b : Module.Basis (Fin n) E (E ⊗[L] M))
    (F : M ≃ₗ[L] M)
    (ha : (LinearMap.toMatrix
      ((b.baseChange Ω).map (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M))
      ((b.baseChange Ω).map (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M))
      (F.baseChange L Ω M M).toLinearMap).IsUpperTriangular) :
    (LinearMap.toMatrix b b (F.baseChange L E M M).toLinearMap).IsUpperTriangular := by
  rw [tower_equiv_matrix E b F] at ha
  intro i j hij
  apply (algebraMap E Ω).injective
  exact (ha hij).trans (map_zero _).symm

private theorem tower_diagonal
    {L Ω M : Type*} [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] {n : ℕ}
    (E : IntermediateField L Ω) (b : Module.Basis (Fin n) E (E ⊗[L] M))
    (F : M ≃ₗ[L] M) (j : Fin n) :
    algebraMap E Ω (b.repr ((F.baseChange L E M M) (b j)) j) =
      (((b.baseChange Ω).map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M)).repr
        ((F.baseChange L Ω M M) (((b.baseChange Ω).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M)) j))) j := by
  have h := congrFun (congrFun (tower_equiv_matrix E b F) j) j
  simpa only [Matrix.map_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe] using h.symm

private theorem tower_unit_diagonal
    {L Ω M : Type*} [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] {n : ℕ}
    (E : IntermediateField L Ω) (b : Module.Basis (Fin n) E (E ⊗[L] M))
    (F : M ≃ₗ[L] M) (α : Fin n → Eˣ)
    (hα : ∀ j, (α j : E) = b.repr ((F.baseChange L E M M) (b j)) j) :
    ∀ j, ((Units.map (algebraMap E Ω).toMonoidHom (α j)) : Ω) =
      (((b.baseChange Ω).map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M)).repr
        ((F.baseChange L Ω M M) (((b.baseChange Ω).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange L E Ω Ω M)) j))) j := by
  intro j
  change algebraMap E Ω (α j : E) = _
  rw [hα]
  exact tower_diagonal E b F j

-- Inlining these cached instances avoids repeated tensor-tower instance comparison.
set_option linter.style.haveILetI false in
set_option maxHeartbeats 600000 in
-- The conclusion packages two full dependent flags over a tensor tower.
/-- A full automorphism flag, its adapted bases, inverse operators and exact sequences
can all be defined over one finite intermediate field.

Source: blueprint, `thm-zl-real-mixed-by-curves`, proof, paragraph 7,
dimension-zero Jordan filtration
(blueprint: lem-zl-automorphism-flag-finite-coefficients).

Proof:
1. By def-weil-vector-space-scalar-extension, extend the given basis and inverse
operator to Ω. For d = 0 take the bottom intermediate field and the empty basis.
2. Apply p-linear-triangular over the algebraically closed field Ω. Lift a basis
of each one-dimensional successive quotient. Reduction modulo the preceding
subspace proves that the resulting family is an adapted basis.
3. By lem-weil-pbc-idempotent-charpoly-rank-nullity, each invariant subspace is
mapped onto itself by the injective operator. Its inverse therefore preserves
it too. Restriction and passage to quotients preserve the inverse identities;
the quotient scalars are units. Both operator matrices are upper triangular.
4. Adjoin to E₀ all entries of the adapted coordinate matrix, its inverse, both
operator matrices, and all quotient scalars and their inverses. Algebraicity
from def-weil-algebraic-closure and
lem-weil-pbc-algebraic-generators-finite-extension make this extension finite.
5. Define b over E by its coordinate matrix in c.baseChange E. The inverse
matrix identities and the intertwining identities hold over E by injectivity
of E → Ω, so b is a basis and the two operator matrices have the required form.
6. Take the initial basis spans. Their dimensions are the initial segment
sizes. Restricted operators are inverse; quotient operators are multiplication
by the chosen units. Initial bases identify inclusions with insertion of zero
and quotient projections with the last coordinate, proving exactness over E.
7. By lem-weil-field-scalar-extension-exact the same canonical sequences remain
exact over Ω. Base change preserves bases, dimensions and inverse identities;
the tensor tower equivalence identifies the resulting flag with one in V.
Repeated eigenvalues and nonzero upper off-diagonal entries are unrestricted.

The quotient of W[j+1] by W[j] is written using the comap along the subtype.
The equivalence q identifies its adapted basis with 1 in the coefficient field.
All matrices over E have entries in that same E by their types. -/
theorem exists_flag_finite_coefficients
    {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (E₀ : IntermediateField K Ω) [FiniteDimensional K E₀]
    {V₀ : Type w} [AddCommGroup V₀] [Module E₀ V₀] [FiniteDimensional E₀ V₀]
    {d : ℕ} (c : Module.Basis (Fin d) E₀ V₀) (F₀ : V₀ ≃ₗ[E₀] V₀) :
    ∃ E : IntermediateField E₀ Ω, FiniteDimensional E₀ E ∧
      ∃ (b : Module.Basis (Fin d) E (E ⊗[E₀] V₀)) (α : Fin d → Eˣ),
        (c.baseChange E).toMatrix b * b.toMatrix (c.baseChange E) = 1 ∧
        b.toMatrix (c.baseChange E) * (c.baseChange E).toMatrix b = 1 ∧
        ((LinearMap.toMatrix b b (F₀.baseChange E₀ E V₀ V₀).toLinearMap).IsUpperTriangular ∧
        (LinearMap.toMatrix b b (F₀.baseChange E₀ E V₀ V₀).symm.toLinearMap).IsUpperTriangular ∧
        (∀ j : Fin (d + 1), Module.finrank E (b.flag j) = j.val) ∧
        (∀ j : Fin (d + 1),
          ∃ a : Module.Basis {i : Fin d // i.castSucc < j} E (b.flag j),
            ∀ i, (a i : E ⊗[E₀] V₀) = b i.val) ∧
        ∃ r : ∀ j : Fin (d + 1), (b.flag j) ≃ₗ[E] (b.flag j),
          (∀ (j : Fin (d + 1)) (x : b.flag j),
            (r j x : E ⊗[E₀] V₀) = (F₀.baseChange E₀ E V₀ V₀) x ∧
            ((r j).symm x : E ⊗[E₀] V₀) = (F₀.baseChange E₀ E V₀ V₀).symm x) ∧
          ∃ q : ∀ j : Fin d, ((b.flag j.succ) ⧸
              ((b.flag j.castSucc).comap (b.flag j.succ).subtype)) ≃ₗ[E] E,
            ∃ g : ∀ j : Fin d, ((b.flag j.succ) ⧸
                ((b.flag j.castSucc).comap (b.flag j.succ).subtype)) ≃ₗ[E]
                ((b.flag j.succ) ⧸ ((b.flag j.castSucc).comap (b.flag j.succ).subtype)),
              (∀ (j : Fin d) (x : b.flag j.succ),
                q j (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  b.repr (x : E ⊗[E₀] V₀) j) ∧
              (∀ (j : Fin d) (x : b.flag j.succ),
                g j (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ (r j.succ x) ∧
                (g j).symm (((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ x) =
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ ((r j.succ).symm x)) ∧
              (∀ (j : Fin d) x, q j (g j x) = (α j : E) * q j x) ∧
              (∀ j : Fin d,
                Function.Injective
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j))) ∧
                Function.Exact
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j)))
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ ∧
                Function.Surjective ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ) ∧
              (∀ j : Fin d,
                Function.Injective (LinearMap.baseChange Ω
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j)))) ∧
                Function.Exact (LinearMap.baseChange Ω
                  (Submodule.inclusion (b.flag_mono (Fin.castSucc_le_succ j))))
                  (LinearMap.baseChange Ω ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ) ∧
                Function.Surjective (LinearMap.baseChange Ω
                  ((b.flag j.castSucc).comap (b.flag j.succ).subtype).mkQ))) ∧
        ∃ bΩ : Module.Basis (Fin d) Ω (Ω ⊗[E₀] V₀),
          bΩ = (b.baseChange Ω).map
            (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₀) ∧
          (∀ j : Fin (d + 1), bΩ.flag j = ((b.flag j).baseChange Ω).map
            (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₀).toLinearMap) ∧
          (LinearMap.toMatrix bΩ bΩ (F₀.baseChange E₀ Ω V₀ V₀).toLinearMap).IsUpperTriangular ∧
          (LinearMap.toMatrix bΩ bΩ (F₀.baseChange E₀ Ω V₀ V₀).symm.toLinearMap).IsUpperTriangular ∧
          (∀ j : Fin (d + 1), Module.finrank Ω (bΩ.flag j) = j.val) ∧
          (∀ j : Fin (d + 1),
            ∃ a : Module.Basis {i : Fin d // i.castSucc < j} Ω (bΩ.flag j),
              ∀ i, (a i : Ω ⊗[E₀] V₀) = bΩ i.val) ∧
          ∃ r : ∀ j : Fin (d + 1), (bΩ.flag j) ≃ₗ[Ω] (bΩ.flag j),
            (∀ (j : Fin (d + 1)) (x : bΩ.flag j),
              (r j x : Ω ⊗[E₀] V₀) = (F₀.baseChange E₀ Ω V₀ V₀) x ∧
              ((r j).symm x : Ω ⊗[E₀] V₀) = (F₀.baseChange E₀ Ω V₀ V₀).symm x) ∧
            ∃ q : ∀ j : Fin d, ((bΩ.flag j.succ) ⧸
                ((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype)) ≃ₗ[Ω] Ω,
              ∃ g : ∀ j : Fin d, ((bΩ.flag j.succ) ⧸
                  ((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype)) ≃ₗ[Ω]
                  ((bΩ.flag j.succ) ⧸ ((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype)),
                (∀ (j : Fin d) (x : bΩ.flag j.succ),
                  q j (((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype).mkQ x) =
                    bΩ.repr (x : Ω ⊗[E₀] V₀) j) ∧
                (∀ (j : Fin d) (x : bΩ.flag j.succ),
                  g j (((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype).mkQ x) =
                    ((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype).mkQ (r j.succ x) ∧
                  (g j).symm (((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype).mkQ x) =
                    ((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype).mkQ ((r j.succ).symm x)) ∧
                (∀ (j : Fin d) x, q j (g j x) = algebraMap E Ω (α j : E) * q j x) ∧
                (∀ j : Fin d,
                  Function.Injective
                    (Submodule.inclusion (bΩ.flag_mono (Fin.castSucc_le_succ j))) ∧
                  Function.Exact
                    (Submodule.inclusion (bΩ.flag_mono (Fin.castSucc_le_succ j)))
                    ((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype).mkQ ∧
                  Function.Surjective
                    ((bΩ.flag j.castSucc).comap (bΩ.flag j.succ).subtype).mkQ) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic E₀ Ω :=
    ⟨fun x ↦ (Algebra.IsAlgebraic.isAlgebraic (R := K) x).tower_top E₀⟩
  let cΩ : Module.Basis (Fin d) Ω (Ω ⊗[E₀] V₀) := c.baseChange Ω
  let fΩ : (Ω ⊗[E₀] V₀) →ₗ[Ω] (Ω ⊗[E₀] V₀) := F₀.toLinearMap.baseChange Ω
  have : FiniteDimensional Ω (Ω ⊗[E₀] V₀) := Module.Finite.of_basis cΩ
  have h := triangular_basis_of_card cΩ fΩ
  let a := h.choose
  have ha : (LinearMap.toMatrix a a fΩ).IsUpperTriangular := h.choose_spec
  have desc := finite_basis_descent c a
  let E := desc.choose
  have hfin : FiniteDimensional E₀ E := desc.choose_spec.1
  let b : Module.Basis (Fin d) E (E ⊗[E₀] V₀) := desc.choose_spec.2.choose
  have hb : (b.baseChange Ω).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₀) = a :=
    desc.choose_spec.2.choose_spec
  have : FiniteDimensional E (E ⊗[E₀] V₀) := Module.Finite.of_basis b
  clear_value b E a
  clear h desc
  letI : Module E₀ E := inferInstance
  letI : Module E E := inferInstance
  letI : Module E Ω := inferInstance
  letI : Module E (E ⊗[E₀] V₀) := inferInstance
  letI : Module Ω (Ω ⊗[E₀] V₀) := inferInstance
  let F : (E ⊗[E₀] V₀) ≃ₗ[E] (E ⊗[E₀] V₀) := F₀.baseChange E₀ E V₀ V₀
  let FΩ : (Ω ⊗[E₀] V₀) ≃ₗ[Ω] (Ω ⊗[E₀] V₀) := F₀.baseChange E₀ Ω V₀ V₀
  let bΩ : Module.Basis (Fin d) Ω (Ω ⊗[E₀] V₀) := (b.baseChange Ω).map
    (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₀)
  have hfΩ : (LinearMap.toMatrix bΩ bΩ FΩ.toLinearMap).IsUpperTriangular := by
    have hbΩ : bΩ = a := hb
    rw [hbΩ]
    exact ha
  have hf := descended_triangular E b F₀ hfΩ
  let α : Fin d → Eˣ := fun j ↦ Units.mk0 (b.repr (F (b j)) j)
    (diagonal_ne_zero b F hf j)
  have hα : ∀ j, (α j : E) = b.repr (F (b j)) j := fun _ ↦ rfl
  refine ⟨E, hfin, b, α, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_, ?_⟩
  · exact ⟨hf, inverse_triangular b F hf,
      triangular_flag_data_tensor (A := Ω) b F hf α hα⟩
  · let αΩ : Fin d → Ωˣ := fun j ↦ (Units.map (algebraMap E Ω).toMonoidHom) (α j)
    have hαΩ := tower_unit_diagonal E b F₀ α hα
    refine ⟨bΩ, rfl, ?_, hfΩ, inverse_triangular bΩ FΩ hfΩ, ?_⟩
    · intro j
      rw [basis_flag_map, flag_base_change]
    · exact triangular_flag_data bΩ FΩ hfΩ αΩ hαΩ

end LinearEquiv
