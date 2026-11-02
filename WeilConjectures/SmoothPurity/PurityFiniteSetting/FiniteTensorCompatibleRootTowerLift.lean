/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A common lift of compatible finite roots

Source: finite reduction of purity, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

private theorem unit_roots_surjective (K : Type u) [Field K] [IsAlgClosed K]
    (l : ℕ) (hl : 0 < l) (z : Kˣ) : ∃ y : Kˣ, y ^ l = z := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z : K) hl
  have hne : y ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_zero_of_lt hl)] at hy
    exact z.ne_zero hy.symm
  refine ⟨Units.mk0 y hne, ?_⟩
  apply Units.ext
  exact hy

private theorem compatible_unit_sequence (K : Type u) [Field K] [IsAlgClosed K]
    (l n : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ (l ^ n) = 1) :
    ∃ z : ℕ → Kˣ, z n = ζ ∧ (∀ j, z (j + 1) ^ l = z j) ∧
      (∀ j, z j ^ (l ^ j) = 1) ∧
      (∀ j, j ≤ n → z j = ζ ^ (l ^ (n - j))) := by
  classical
  choose step hstep using unit_roots_surjective K l hl
  let z (j : ℕ) : Kˣ := if j ≤ n then ζ ^ (l ^ (n - j)) else step^[j - n] ζ
  have hzstep (j : ℕ) : z (j + 1) ^ l = z j := by
    by_cases hj : j + 1 ≤ n
    · have hj' : j ≤ n := by omega
      dsimp only [z]
      rw [if_pos hj, if_pos hj', ← pow_mul]
      congr 1
      rw [← pow_succ, show n - (j + 1) + 1 = n - j by omega]
    · by_cases hj' : j ≤ n
      · have heq : j = n := by omega
        subst j
        simp only [z, Nat.le_refl, if_pos, Nat.sub_self, pow_zero, pow_one,
          Nat.not_succ_le_self, if_false, Nat.add_sub_cancel_left, Function.iterate_one]
        exact hstep ζ
      · dsimp only [z]
        rw [if_neg hj, if_neg hj', show j + 1 - n = (j - n) + 1 by omega,
          Function.iterate_succ_apply', hstep]
  have hzpow (j : ℕ) : z j ^ (l ^ j) = 1 := by
    by_cases hj : j ≤ n
    · dsimp only [z]
      rw [if_pos hj, ← pow_mul, ← pow_add, Nat.sub_add_cancel hj]
      exact hζ
    · have hrel (k : ℕ) : z (n + k) ^ (l ^ k) = ζ := by
        induction k with
        | zero => simp [z]
        | succ k ih =>
          rw [pow_succ', pow_mul, show n + (k + 1) = (n + k) + 1 by omega,
            hzstep, ih]
      have hh := hrel (j - n)
      rw [Nat.add_sub_cancel' (Nat.le_of_not_ge hj)] at hh
      calc
        z j ^ (l ^ j) = (z j ^ (l ^ (j - n))) ^ (l ^ n) := by
          rw [← pow_mul, ← pow_add, Nat.sub_add_cancel (by omega : n ≤ j)]
        _ = 1 := (congrArg (fun a : Kˣ ↦ a ^ (l ^ n)) hh).trans hζ
  exact ⟨z, by simp [z], hzstep, hzpow, fun j hj ↦ by simp [z, hj]⟩

/-- Compatible primitive roots have a common section of the integral root tower.
Source: finite reduction of purity, Step 2; the root-lifting argument of Stacks 03PK.
(blueprint: lem-pur-finite-tensor-compatible-root-tower-lift)
Proof: choose successive ell-th roots in the algebraically closed base field above
zeta. Below the prescribed level take its iterated ell-power images. These roots
have orders dividing the corresponding powers of ell and satisfy the transition
identities. Map their units to the sections of V through its structure morphism.
The sectionwise inverse-limit universal property gives a section of the root
sheaf. Its level-n coordinate is zeta, and its level-m coordinate is eta by the
hypothesized power relation. The inclusion of each root sheaf into the units sheaf
identifies these coordinates with the two displayed underlying units. This uses
no nonemptiness hypothesis on V. -/
theorem finiteTensor_compatible_root_tower_lift
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (η : P.field.k)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) (V : T.ProEt) :
    ∃ t : (purTwistZlOne T P.coefficients.l).obj.obj (Opposite.op V),
      (finiteTateLimitRootValue P.coefficients.l T (P.level - 1) (Opposite.op V) t :
        Γ(V.left, ⊤)) =
          ((ΓSpecIso (.of P.field.k)).inv ≫
            (V.hom ≫ (T ↘ Spec (.of P.field.k))).appTop).hom ζ ∧
      (finiteTateLimitRootValue P.coefficients.l T (m - 1) (Opposite.op V) t :
        Γ(V.left, ⊤)) =
          ((ΓSpecIso (.of P.field.k)).inv ≫
            (V.hom ≫ (T ↘ Spec (.of P.field.k))).appTop).hom η := by
  classical
  let l := P.coefficients.l
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let ζu : P.field.kˣ := (hζ.isUnit (NeZero.ne P.diagonalExponent)).unit
  have hζu : ζu ^ (l ^ P.level) = 1 := by
    apply Units.ext
    change (ζu : P.field.k) ^ P.diagonalExponent = 1
    simpa only [ζu, IsUnit.unit_spec] using hζ.pow_eq_one
  obtain ⟨z, hzn, hzstep, hzpow, hzlower⟩ :=
    compatible_unit_sequence P.field.k l P.level hl ζu hζu
  let ρ : P.field.k →+* Γ(V.left, ⊤) :=
    ((ΓSpecIso (.of P.field.k)).inv ≫
      (V.hom ≫ (T ↘ Spec (.of P.field.k))).appTop).hom
  let w (r : ℕ) : Γ(V.left, ⊤)ˣ := Units.map ρ.toMonoidHom (z (r + 1))
  have hwpow (r : ℕ) : w r ^ (l ^ (r + 1)) = 1 := by
    exact (map_pow (Units.map ρ.toMonoidHom) _ _).symm.trans
      ((congrArg (Units.map ρ.toMonoidHom) (hzpow (r + 1))).trans
        (map_one (Units.map ρ.toMonoidHom)))
  let y (r : ℕ) :
      (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (Opposite.op V) :=
    (proEtaleRootsOfUnitySections T (l ^ (r + 1)) (Opposite.op V)).symm
      (Additive.ofMul ⟨w r, (mem_rootsOfUnity _ _).mpr (hwpow r)⟩)
  have hy (r : ℕ) : (proEtaleRootsOfUnityInclusion T (l ^ (r + 1))).hom.app
      (Opposite.op V) (y r) = ULift.up (Additive.ofMul (w r)) := by
    have h := (existsUnique_proEtaleRootsOfUnitySections T (l ^ (r + 1))
      (Opposite.op V)).exists.choose_spec (y r)
    change ULift.up (Additive.ofMul
      (((proEtaleRootsOfUnitySections T (l ^ (r + 1)) (Opposite.op V)) (y r)).toMul.val)) =
        _ at h
    have he : (proEtaleRootsOfUnitySections T (l ^ (r + 1)) (Opposite.op V)) (y r) =
        Additive.ofMul ⟨w r, (mem_rootsOfUnity _ _).mpr (hwpow r)⟩ :=
      AddEquiv.apply_symm_apply _ _
    rw [he] at h
    exact h.symm
  have hic (r : ℕ) : Function.Injective
      ((proEtaleRootsOfUnityInclusion T (l ^ (r + 1))).hom.app (Opposite.op V)) := by
    have : Mono (proEtaleRootsOfUnityInclusion T (l ^ (r + 1))) := by
      dsimp [proEtaleRootsOfUnityInclusion]
      infer_instance
    have : Mono (proEtaleRootsOfUnityInclusion T (l ^ (r + 1))).hom :=
      (sheafToPresheaf _ _).map_mono _
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  let D := proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)
  have hcompat (r : ℕ) : (D.map (homOfLE (Nat.le_succ r)).op).hom.app
      (Opposite.op V) (y (r + 1)) = y r := by
    have hd : D.map (homOfLE (Nat.le_succ r)).op =
      proEtaleRootsOfUnityTransition T (l ^ (r + 1)) (l ^ (r + 2))
        (pow_pos hl _) (pow_pos hl _)
        (pow_dvd_pow l (Nat.le_succ (r + 1))) :=
          Functor.ofOpSequence_map_homOfLE_succ _ r
    simp only [hd]
    change (proEtaleRootsOfUnityTransition T (l ^ (r + 1)) (l ^ (r + 2))
      (pow_pos hl _) (pow_pos hl _)
      (pow_dvd_pow l (Nat.le_succ (r + 1)))).hom.app (Opposite.op V)
      (y (r + 1)) = y r
    apply hic r
    rw [proEtaleRootsOfUnityTransition_prime T l (Fact.out : l.Prime), hy, hy]
    apply ULift.ext
    apply Additive.toMul.injective
    change (w (r + 1)) ^ l = w r
    change (Units.map ρ.toMonoidHom (z ((r + 1) + 1))) ^ l =
      Units.map ρ.toMonoidHom (z (r + 1))
    rw [← map_pow, hzstep]
  let ev := sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation T.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op V)
  let c : Cone (D ⋙ ev ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    { pt := PUnit
      π := NatTrans.ofOpSequence (fun r ↦ ↾fun _ ↦ y r) (by
        intro r
        ext a
        exact (hcompat r).symm) }
  let hc := isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1})
    (isLimitOfPreserves ev (limit.isLimit D))
  let t : (purTwistZlOne T l).obj.obj (Opposite.op V) := hc.lift c PUnit.unit
  have ht (r : ℕ) : finiteTateLimitRootValue l T r (Opposite.op V) t = w r := by
    have hfac := ConcreteCategory.congr_hom (hc.fac c (Opposite.op r)) PUnit.unit
    change (limit.π D (Opposite.op r)).hom.app (Opposite.op V) t = y r at hfac
    unfold finiteTateLimitRootValue
    rw [hfac, hy]
    rfl
  refine ⟨t, ?_, ?_⟩
  · rw [ht]
    change ρ (z (P.level - 1 + 1) : P.field.k) = ρ ζ
    rw [show P.level - 1 + 1 = P.level by omega, hzn]
    rw [show (ζu : P.field.k) = ζ from (hζ.isUnit (NeZero.ne P.diagonalExponent)).unit_spec]
  · rw [ht]
    change ρ ((z (m - 1 + 1)) : P.field.k) = ρ η
    rw [show m - 1 + 1 = m by omega, hzlower m hmn]
    change ρ ((ζu : P.field.k) ^ (l ^ (P.level - m))) = ρ η
    rw [show (ζu : P.field.k) = ζ from (hζ.isUnit (NeZero.ne P.diagonalExponent)).unit_spec, hroot]


end WeilConjectures.PurityFiniteSetting
