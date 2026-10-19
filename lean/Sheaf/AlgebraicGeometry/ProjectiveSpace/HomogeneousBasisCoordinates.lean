/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Coordinates of a homogeneous basis

Source: Stacks Project, Constructions, Tags 01M6 and 01MN; the coordinate step of
lem-sc-p1-homogeneous-basis-proj-coproduct.
(blueprint: lem-sc-p1-homogeneous-basis-coordinates)
-/

@[expose] public section

universe u

open MvPolynomial

namespace AlgebraicGeometry.Proj

/-- Coordinates of a homogeneous vector have the degrees prescribed by its basis.
Source: Stacks Project, Constructions, Tags 01M6 and 01MN; step 1 of
lem-sc-p1-homogeneous-basis-proj-coproduct.
(blueprint: lem-sc-p1-homogeneous-basis-coordinates)

Proof: Expand each coordinate polynomial into its finitely many homogeneous components.
The component of degree n in coordinate a, multiplied by b a, lies in M_(n-d a).
Regroup the resulting finite sum by the integer n-d a. Apply uniqueness of the internal
additive decomposition of M to a vector in M_j: every grouped sum of degree other than
j is zero. Linear independence of b implies each coefficient in each such grouped sum
is zero. For each a at most one nonnegative n satisfies n-d a=j. Thus its coordinate
is homogeneous of degree d a+j when that integer is nonnegative, and otherwise zero.
The argument includes a zero vector and an empty basis. -/
theorem homogeneous_basis_coordinates (k : Type u) [Field k]
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (r : ℕ) (d : Fin r → ℤ)
    (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) M)
    (hb : ∀ a : Fin r, b a ∈ 𝓜 (-(d a)))
    (j : ℤ) (y : M) (hy : y ∈ 𝓜 j) :
    ∀ a, if 0 ≤ d a + j then
      b.equivFun y a ∈ homogeneousSubmodule (Fin 2) k (d a + j).toNat
    else b.equivFun y a = 0 := by
  classical
  let := h𝓜.chooseDecomposition
  let P (z : ℤ) : M →+ M :=
    ((𝓜 z).subtype.comp (DFinsupp.evalAddMonoidHom z)).comp
      (DirectSum.decomposeAddEquiv 𝓜).toAddMonoidHom
  have hP (z : ℤ) (n : ℕ) (i : Fin r) :
      P z (homogeneousComponent n (b.equivFun y i) • b i) =
        if (n : ℤ) - d i = z then homogeneousComponent n (b.equivFun y i) • b i
        else 0 := by
    have ht := hsmul n (-(d i)) (homogeneousComponent n (b.equivFun y i))
      (b i) (homogeneousComponent_mem n _) (hb i)
    change (DirectSum.decompose 𝓜 _ z : M) = _
    by_cases hz : (n : ℤ) - d i = z
    · rw [if_pos hz]
      apply DirectSum.decompose_of_mem_same
      simpa only [← sub_eq_add_neg, hz] using ht
    · rw [if_neg hz]
      exact DirectSum.decompose_of_mem_ne 𝓜 ht (by simpa [sub_eq_add_neg] using hz)
  have hsum (z : ℤ) : P z y = ∑ i : Fin r,
      ∑ n ∈ Finset.range ((b.equivFun y i).totalDegree + 1),
        if (n : ℤ) - d i = z then homogeneousComponent n (b.equivFun y i) • b i
        else 0 := by
    conv_lhs => rw [← b.sum_equivFun y]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => rw [← sum_homogeneousComponent (b.equivFun y i)]
    rw [Finset.sum_smul, map_sum]
    apply Finset.sum_congr rfl
    intro n _
    exact hP z n i
  have hcoord (z : ℤ) (a : Fin r) : b.equivFun (P z y) a =
      ∑ n ∈ Finset.range ((b.equivFun y a).totalDegree + 1),
        if (n : ℤ) - d a = z then homogeneousComponent n (b.equivFun y a) else 0 := by
    rw [hsum]
    simp only [map_sum, apply_ite, ite_apply, map_smul, map_zero, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, Module.Basis.equivFun_self]
    rw [Finset.sum_eq_single a]
    · simp [smul_eq_mul]
    · intro i _ hia
      apply Finset.sum_eq_zero
      intro n _
      simp [hia, smul_eq_mul]
    · simp
  have hPy : P j y = y := DirectSum.decompose_of_mem_same 𝓜 hy
  intro a
  have hc (n : ℕ) (hn : (n : ℤ) - d a ≠ j) :
      homogeneousComponent n (b.equivFun y a) = 0 := by
    have H := congrArg (homogeneousComponent n) (hcoord j a)
    rw [hPy] at H
    rw [H]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : (t : ℤ) - d a = j
    · rw [if_pos ht, homogeneousComponent_of_mem (homogeneousComponent_mem t _)]
      have hnt : n ≠ t := by omega
      simp [hnt]
    · simp [ht]
  split_ifs with ha
  · have heq : b.equivFun y a =
        homogeneousComponent (d a + j).toNat (b.equivFun y a) := by
      apply MvPolynomial.ext
      intro m
      by_cases hm : m.degree = (d a + j).toNat
      · simp [coeff_homogeneousComponent, hm]
      · have h := congrArg (MvPolynomial.coeff m) (hc m.degree (by
          have hcast := Int.toNat_of_nonneg ha
          omega))
        simpa [coeff_homogeneousComponent, hm] using h
    rw [heq]
    exact homogeneousComponent_mem _ _
  · rw [← sum_homogeneousComponent (b.equivFun y a)]
    apply Finset.sum_eq_zero
    intro n _
    exact hc n (by omega)

end AlgebraicGeometry.Proj
