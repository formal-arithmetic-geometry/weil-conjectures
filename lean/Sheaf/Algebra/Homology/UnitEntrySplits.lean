/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Splitting off a unit entry in a finite free chain complex

Source: Stacks Project, Algebra, Lemma 10.102.2, Tag 00MT
(blueprint: lem-weil-pbc-free-complex-unit-entry-splits).
-/

@[expose] public section

universe u v

open scoped DirectSum

namespace ChainComplex

/-- A unit matrix entry splits off the identity complex in degrees `i` and `i - 1`.
Source: Stacks Project, Algebra, Lemma 10.102.2, Tag 00MT
(blueprint: lem-weil-pbc-free-complex-unit-entry-splits).

The natural numbers `n j` are the sizes of the chosen bases, as in the source's `R^{n_j}`.
The unit coefficient is the entry `(q, p)` of the matrix `LinearMap.toMatrix (b i) (b (i - 1))`
of `d_i` in the bases `b i` and `b (i - 1)`.
This formulation includes the zero ring. The binary direct sum is `DirectSum` indexed by
`Bool`; `false` selects the complementary complex and `true` selects the identity complex.
Its differential acts componentwise, and `ψ` intertwines these differentials on every pair
of summand elements, hence on every element of the binary direct sum.
The equivalences `e` and `f` identify the two nonzero terms of `T` with `R`; their compatibility
says that the differential becomes the identity under those identifications.

Proof: (1) Move the unit coefficient to the first position. Replace the first target basis
vector by the image of the first source basis vector. The triangular coefficient matrix has
unit diagonal, so this is a basis by `lem-weil-pbc-triangular-change-of-basis`.
(2) Subtract from each remaining source basis vector its first image coefficient times the
first source basis vector. Again the triangular change of basis has unit diagonal, by that
same lemma. The differential now has an isolated identity entry.
(3) The spans of the remaining basis vectors give finite free complementary modules in the
two degrees, with one fewer basis vector in each (`def-weil-pbc-free-module`).
(4) The incoming differential lands in the source complement: its image has first coefficient
zero because two consecutive differentials compose to zero.
(5) The outgoing differential kills the first target basis vector, since it is itself an image.
(6) Restrict the differentials to obtain `C'`. Take `T` to be the identity on `R` in the two
degrees and zero elsewhere. Add the two complementary components to define `ψ` degreewise
(`def-weil-pbc-direct-sum-modules`). Steps (3)--(5) give linear bijectivity and compatibility
with every differential; the restricted differentials still square to zero. -/
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
  sorry

end ChainComplex
