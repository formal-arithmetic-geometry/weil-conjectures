/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.LinearAlgebra.KernelBasisOfUnitValue
import WeilConjectures.Algebra.Homology.SplitIdentityFromFunctionals

/-!
# Splitting off a unit entry in a finite free chain complex

## Implementation details

The natural numbers `n j` are the sizes of the chosen bases. The unit coefficient is the entry
`(q, p)` of the matrix `LinearMap.toMatrix (b i) (b (i - 1))` of `d_i`. The binary direct sum is
`DirectSum` indexed by `Bool`: `false` selects the complementary complex and `true` selects
the identity complex.

## References

* Stacks Project, Algebra, Lemma 10.102.2, Tag 00MT
-/

@[expose] public section

universe u v

open scoped DirectSum

namespace ChainComplex

/-- A unit matrix entry splits off the identity complex in degrees `i` and `i - 1`. -/
theorem exists_splitting_of_isUnit_entry
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℤ)
    (n : ℤ → ℕ) (b : ∀ j : ℤ, Module.Basis (Fin (n j)) R (C.X j))
    (i : ℤ) (p : Fin (n i)) (q : Fin (n (i - 1)))
    (hunit : IsUnit (LinearMap.toMatrix (b i) (b (i - 1)) (C.d i (i - 1)).hom q p)) :
    ∃ (C' T : ChainComplex (ModuleCat.{max u v} R) ℤ) (n' : ℤ → ℕ),
      (∀ j : ℤ, Nonempty (Module.Basis (Fin (n' j)) R (C'.X j))) ∧
      n' i + 1 = n i ∧ n' (i - 1) + 1 = n (i - 1) ∧
      (∀ j : ℤ, j ≠ i → j ≠ i - 1 → n' j = n j) ∧
      (∀ j : ℤ, j ≠ i → j ≠ i - 1 → Subsingleton (T.X j)) ∧
      ∃ (e : T.X i ≃ₗ[R] R) (f : T.X (i - 1) ≃ₗ[R] R),
        (∀ t : T.X i, f ((T.d i (i - 1)).hom t) = e t) ∧
        let M : ℤ → Bool → ModuleCat.{max u v} R :=
          fun j s ↦ if s then T.X j else C'.X j
        ∃ ψ : ∀ j : ℤ, (⨁ s : Bool, M j s) ≃ₗ[R] C.X j,
          ∀ (j : ℤ) (x : C'.X j) (t : T.X j),
            (C.d j (j - 1)).hom
                (ψ j (DirectSum.lof R Bool (fun s ↦ M j s) false x +
                  DirectSum.lof R Bool (fun s ↦ M j s) true t)) =
              ψ (j - 1)
                (DirectSum.lof R Bool (fun s ↦ M (j - 1) s) false
                    ((C'.d j (j - 1)).hom x) +
                  DirectSum.lof R Bool (fun s ↦ M (j - 1) s) true
                    ((T.d j (j - 1)).hom t)) := by
  classical
  let a := LinearMap.toMatrix (b i) (b (i - 1)) (C.d i (i - 1)).hom q p
  obtain ⟨u, hu⟩ := hunit
  have hcoord : (b (i - 1)).coord q ((C.d i (i - 1)).hom ((b i) p)) = a := by
    simp [a, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
  let β : C.X (i - 1) →ₗ[R] R := (↑(u⁻¹) : R) • (b (i - 1)).coord q
  let α : C.X i →ₗ[R] R := β.comp (C.d i (i - 1)).hom
  let z : C.X i := (b i) p
  let w : C.X (i - 1) := (C.d i (i - 1)).hom z
  have hw : β w = 1 := by
    change (↑(u⁻¹) : R) * (b (i - 1)).coord q
      ((C.d i (i - 1)).hom ((b i) p)) = 1
    rw [hcoord]
    change (↑(u⁻¹) : R) *
      LinearMap.toMatrix (b i) (b (i - 1)) (C.d i (i - 1)).hom q p = 1
    rw [← hu]
    simp
  have hz : α z = 1 := hw
  have hα : IsUnit (α ((b i) p)) := by rw [hz]; exact isUnit_one
  have hβ : IsUnit (β ((b (i - 1)) q)) := by
    simp [β, Module.Basis.coord_apply]
  obtain ⟨bi⟩ := (b i).exists_basis_ker_of_isUnit_value α p hα
  obtain ⟨bj⟩ := (b (i - 1)).exists_basis_ker_of_isUnit_value β q hβ
  have hin : ∀ x, α ((C.d (i + 1) i).hom x) = 0 := by
    intro x
    have hzero : (C.d i (i - 1)).hom ((C.d (i + 1) i).hom x) = 0 := by
      have h := congrArg (fun f => f.hom x) (C.d_comp_d (i + 1) i (i - 1))
      change (C.d i (i - 1)).hom ((C.d (i + 1) i).hom x) = 0 at h
      exact h
    change β ((C.d i (i - 1)).hom ((C.d (i + 1) i).hom x)) = 0
    rw [hzero, map_zero]
  have hout : (C.d (i - 1) (i - 2)).hom w = 0 := by
    have h := congrArg (fun f => f.hom z) (C.d_comp_d i (i - 1) (i - 2))
    change (C.d (i - 1) (i - 2)).hom ((C.d i (i - 1)).hom z) = 0 at h
    exact h
  obtain ⟨C', T, g, hT, e, f, hef, ψ, hψ⟩ :=
    exists_splitting_of_split_functionals C i α β z w hz hw (fun _ => rfl) rfl hin hout
  let S : ∀ j : ℤ, Submodule R (C.X j) := fun j ↦
    if h : j = i then h ▸ LinearMap.ker α
    else if h : j = i - 1 then h ▸ LinearMap.ker β else ⊤
  change ∀ j, C'.X j ≃ₗ[R] S j at g
  let n' : ℤ → ℕ := fun j => if j = i then n i - 1
    else if j = i - 1 then n (i - 1) - 1 else n j
  have hii : i - 1 ≠ i := by omega
  refine ⟨C', T, n', ?_, ?_, ?_, ?_, hT, e, f, hef, ψ, hψ⟩
  · intro j
    by_cases hi : j = i
    · subst j
      have hS : S i = LinearMap.ker α := by simp [S]
      let g' := (g i).trans (LinearEquiv.ofEq _ _ hS)
      simpa only [n', ite_true] using Nonempty.intro (bi.map g'.symm)
    · by_cases hj : j = i - 1
      · subst j
        have hS : S (i - 1) = LinearMap.ker β := by simp [S, hii]
        let g' := (g (i - 1)).trans (LinearEquiv.ofEq _ _ hS)
        simpa only [n', ite_eq_right hii, ite_true] using Nonempty.intro (bj.map g'.symm)
      · have hS : S j = ⊤ := by simp [S, hi, hj]
        let g' := (g j).trans (LinearEquiv.ofEq _ _ hS)
        let e' := g'.trans (Submodule.topEquiv : _ ≃ₗ[R] _)
        simpa only [n', ite_eq_right hi, ite_eq_right hj] using Nonempty.intro ((b j).map e'.symm)
  · have hp := p.isLt
    simp only [n', ite_true]
    omega
  · have hq := q.isLt
    simp only [n', ite_eq_right hii, ite_true]
    omega
  · intro j hi hj
    simp [n', hi, hj]

end ChainComplex
