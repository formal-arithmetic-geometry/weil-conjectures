/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.TotalResolutionCycleFiniteSupport
import WeilConjectures.AlgebraicGeometry.TotalResolutionCycleSupportStep
import WeilConjectures.AlgebraicGeometry.TotalResolutionCycleSupportZero

/-!
# Cycle reduction for left half-plane total complexes

For a double complex concentrated in nonpositive columns whose columnwise homology rows are exact
far to the left, every cycle of the total complex is homologous to a cycle of column zero.

## References

* [Stacks Project, Tag 09IZ](https://stacks.math.columbia.edu/tag/09IZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- Finite-support reduction for the left half-plane total complex. -/
theorem total_resolution_column_zero_cycle_reduction
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (j : K.X 0 ⟶ K.total (ComplexShape.up ℤ))
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (hj : ∀ q, j.f q = K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp))
    (h_homology : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.homologyMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.homologyMap (K.d (p + 1) (p + 2)) q).hom) :
    ∀ z : (K.total (ComplexShape.up ℤ)).cycles n,
      ∃ y : (K.X 0).cycles n, ∃ b : (K.total (ComplexShape.up ℤ)).X (n - 1),
        (K.total (ComplexShape.up ℤ)).iCycles n z =
          j.f n ((K.X 0).iCycles n y) +
            (K.total (ComplexShape.up ℤ)).d (n - 1) n b := by
  have hind : ∀ r : ℕ, ∀ z : (K.total (ComplexShape.up ℤ)).cycles n,
      (∃ x : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)),
        (K.total (ComplexShape.up ℤ)).iCycles n z =
          Finset.sum (Finset.range (r + 1)) (fun i =>
            K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i))) →
      ∃ y : (K.X 0).cycles n, ∃ b : (K.total (ComplexShape.up ℤ)).X (n - 1),
        (K.total (ComplexShape.up ℤ)).iCycles n z =
          j.f n ((K.X 0).iCycles n y) +
            (K.total (ComplexShape.up ℤ)).d (n - 1) n b := by
    intro r
    induction r with
    | zero =>
        rintro z ⟨x, hx⟩
        let a : (K.X 0).X n :=
          (K.XXIsoOfEq _ _ _ (by simp : -(0 : ℤ) = 0) (add_zero n)).hom (x 0)
        have he := congrArg (fun f => f (x 0))
          (K.XXIsoOfEq_hom_ιTotal (ComplexShape.up ℤ)
            (by simp : -(0 : ℤ) = 0) (add_zero n) n (by simp))
        change K.ιTotal (ComplexShape.up ℤ) 0 n n (by simp) a =
          K.ιTotal (ComplexShape.up ℤ) (-(0 : ℤ)) (n + 0) n (by simp) (x 0) at he
        have ha : (K.total (ComplexShape.up ℤ)).iCycles n z = j.f n a := by
          rw [hj, he]
          simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton] at hx
          change (K.total (ComplexShape.up ℤ)).iCycles n z =
            K.ιTotalOrZero (ComplexShape.up ℤ) (-(0 : ℤ)) (n + 0) n (x 0) at hx
          rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (-(0 : ℤ)) (n + 0) n (by simp)] at hx
          exact hx
        obtain ⟨y, hy⟩ := total_resolution_cycle_support_zero K j n hj z a ha
        exact ⟨y, 0, by simpa using hy⟩
    | succ r ih =>
        rintro z ⟨x, hx⟩
        obtain ⟨z', x', b, hx', hb⟩ :=
          total_resolution_cycle_support_step K n h_homology r z x hx
        obtain ⟨y, b', hy⟩ := ih z' ⟨x', hx'⟩
        refine ⟨y, b' + b, ?_⟩
        rw [hb, hy, map_add, add_assoc]
  intro z
  obtain ⟨r, x, hx⟩ := total_resolution_element_finite_support K n h_positive
    ((K.total (ComplexShape.up ℤ)).iCycles n z)
  exact hind r z ⟨x, hx⟩

end WeilConjectures.DerivedTotalResolution
