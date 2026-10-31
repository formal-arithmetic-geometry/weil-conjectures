/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The normalized cokernel of a rectangular rank matrix

Source: Stacks Project, Tag 00DF; Bhatt--Scholze, Proposition 6.8.14(2),
finite-presentation calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace Matrix

private def rankBlock (R : Type u) [CommRing R] (m n ρ : ℕ) :
    Matrix (Fin n) (Fin m) R :=
  fun i j ↦ if i.val = j.val ∧ i.val < ρ then 1 else 0

private theorem rankBlock_apply {R : Type u} [CommRing R] {m n ρ : ℕ}
    (hρm : ρ ≤ m) (x : Fin m → R) (i : Fin n) :
    (rankBlock R m n ρ).mulVec x i =
      if hi : i.val < ρ then x ⟨i.val, hi.trans_le hρm⟩ else 0 := by
  classical
  dsimp only [Matrix.mulVec, dotProduct, rankBlock]
  by_cases hi : i.val < ρ
  · rw [dif_pos hi]
    let j : Fin m := ⟨i.val, hi.trans_le hρm⟩
    rw [Finset.sum_eq_single j]
    · simp [j, hi]
    · intro k _ hk
      have hne : i.val ≠ k.val := fun h ↦ hk (Fin.ext h.symm)
      simp [hne]
    · simp
  · simp [hi]

private def tailMap (R : Type u) [CommRing R] {n ρ : ℕ} (hρn : ρ ≤ n) :
    (Fin n → R) →ₗ[R] (Fin (n - ρ) → R) :=
  LinearMap.funLeft R R (fun j ↦ Fin.cast (Nat.add_sub_of_le hρn) (Fin.natAdd ρ j))

private theorem rankBlock_exact {R : Type u} [CommRing R] {m n ρ : ℕ}
    (hρn : ρ ≤ n) (hρm : ρ ≤ m) :
    Function.Exact (Matrix.toLin' (rankBlock R m n ρ)) (tailMap R hρn) := by
  intro x
  constructor
  · intro hx
    let y : Fin m → R := fun j ↦ if hj : j.val < ρ then
      x ⟨j.val, hj.trans_le hρn⟩ else 0
    refine ⟨y, ?_⟩
    funext i
    rw [Matrix.toLin'_apply, rankBlock_apply hρm]
    by_cases hi : i.val < ρ
    · simp [hi, y]
    · rw [dif_neg hi]
      let j : Fin (n - ρ) := ⟨i.val - ρ, by omega⟩
      have he : Fin.cast (Nat.add_sub_of_le hρn) (Fin.natAdd ρ j) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      have hh := congrFun hx j
      change x (Fin.cast (Nat.add_sub_of_le hρn) (Fin.natAdd ρ j)) = 0 at hh
      exact (he ▸ hh).symm
  · rintro ⟨y, rfl⟩
    funext j
    change (rankBlock R m n ρ).mulVec y
      (Fin.cast (Nat.add_sub_of_le hρn) (Fin.natAdd ρ j)) = 0
    rw [rankBlock_apply hρm, dif_neg]
    simp only [Fin.val_cast, Fin.val_natAdd]
    omega

private theorem tailMap_surjective {R : Type u} [CommRing R] {n ρ : ℕ}
    (hρn : ρ ≤ n) : Function.Surjective (tailMap R hρn) := by
  intro x
  refine ⟨fun i ↦ if hi : ρ ≤ i.val then x ⟨i.val - ρ, by omega⟩ else 0, ?_⟩
  funext j
  change (if hi : ρ ≤ ρ + j.val then
    x ⟨ρ + j.val - ρ, by omega⟩ else 0) = x j
  simp

/-- The tail of an invertible row operation is the normalized quotient by a matrix
whose supplied row and column operations put it in rectangular rank normal form.
Source: Stacks Project, Tag 00DF; Bhatt--Scholze, Proposition 6.8.14(2).
(blueprint: lem-per-rank-normal-cokernel).

Proof: For the rectangular rank matrix, its image consists exactly of vectors whose
tail is zero. A vector with zero tail is the image of its first rho coordinates,
padded by zeros; the bound rho <= m makes this a vector in the source. Tail extraction
is surjective by zero padding in the target. Thus it is the cokernel projection.
Invertible row and column changes carry this cokernel to the original matrix; its
projection is tail extraction after the supplied row operation. This works unchanged
for empty source or target and for a zero-dimensional tail. -/
theorem rankNormalCokernel {R : Type u} [CommRing R] {m n ρ : ℕ}
    (D : Matrix (Fin n) (Fin m) R) (hρn : ρ ≤ n) (hρm : ρ ≤ m)
    (P : GeneralLinearGroup (Fin n) R) (Q : GeneralLinearGroup (Fin m) R)
    (hnorm : (P : Matrix (Fin n) (Fin n) R) * D *
      (Q : Matrix (Fin m) (Fin m) R) =
        fun i j ↦ if i.val = j.val ∧ i.val < ρ then 1 else 0) :
    ∃ a : cokernel (ModuleCat.ofHom (Matrix.toLin' D)) ≅
        ModuleCat.of R (Fin (n - ρ) → R),
      ∀ (x : Fin n → R) (j : Fin (n - ρ)),
        a.hom (cokernel.π (ModuleCat.ofHom (Matrix.toLin' D)) x) j =
          (P : Matrix (Fin n) (Fin n) R).mulVec x
            (Fin.cast (Nat.add_sub_of_le hρn) (Fin.natAdd ρ j)) := by
  let p : ModuleCat.of R (Fin n → R) ≅ ModuleCat.of R (Fin n → R) :=
    (GeneralLinearGroup.toLin P).toLinearEquiv.toModuleIso
  let q : ModuleCat.of R (Fin m → R) ≅ ModuleCat.of R (Fin m → R) :=
    (GeneralLinearGroup.toLin Q).toLinearEquiv.toModuleIso
  let d := ModuleCat.ofHom (Matrix.toLin' D)
  let e := ModuleCat.ofHom (Matrix.toLin' (rankBlock R m n ρ))
  have he : d ≫ p.hom = q.inv ≫ e := by
    have hh : (P : Matrix (Fin n) (Fin n) R) * D =
        rankBlock R m n ρ *
          ((Q⁻¹ : GeneralLinearGroup (Fin m) R) : Matrix (Fin m) (Fin m) R) := by
      have hnorm' : (P : Matrix (Fin n) (Fin n) R) * D *
          (Q : Matrix (Fin m) (Fin m) R) = rankBlock R m n ρ := hnorm
      rw [← hnorm', Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (P : Matrix (Fin n) (Fin n) R).mulVec (D.mulVec x) =
      (rankBlock R m n ρ).mulVec
        (((Q⁻¹ : GeneralLinearGroup (Fin m) R) : Matrix (Fin m) (Fin m) R).mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh]
  let c := ModuleCat.isColimitCokernelCofork e
    (ModuleCat.ofHom (tailMap R hρn)) (rankBlock_exact hρn hρm) (tailMap_surjective hρn)
  let b : cokernel e ≅ ModuleCat.of R (Fin (n - ρ) → R) :=
    (colimit.isColimit _).coconePointUniqueUpToIso c
  let a := cokernel.mapIso d e q.symm p he ≪≫ b
  refine ⟨a, ?_⟩
  intro x j
  have ha : cokernel.π d ≫ a.hom = p.hom ≫ ModuleCat.ofHom (tailMap R hρn) := by
    dsimp only [a, Iso.trans_hom]
    rw [cokernel.mapIso_hom, cokernel.map, cokernel.π_desc_assoc]
    exact congrArg (p.hom ≫ ·) ((colimit.isColimit _).comp_coconePointUniqueUpToIso_hom c
      WalkingParallelPair.one)
  exact congrFun (ConcreteCategory.congr_hom ha x) j

end Matrix
