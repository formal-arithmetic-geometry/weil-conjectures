/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Eigenvalues of an endomorphism of a vector space over an algebraically closed field

Over an algebraically closed field, the characteristic polynomial of an endomorphism `f` of a
finite dimensional vector space factors as `∏ (X - λ)` over its roots, its reverse factors as
`∏ (1 - λ * X)`, the number of roots is the dimension and their product is the determinant of
`f`; in particular `0` is not a root as soon as `f` is invertible.
-/

@[expose] public section

open Module Polynomial

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [IsAlgClosed K]

theorem charpoly_eq_prod_roots (f : V →ₗ[K] V) :
    f.charpoly = (f.charpoly.roots.map fun a ↦ X - C a).prod :=
  (IsAlgClosed.splits _).eq_prod_roots_of_monic f.charpoly_monic

theorem charpolyRev_eq_prod_roots (f : V →ₗ[K] V) :
    f.charpolyRev = (f.charpoly.roots.map fun a ↦ 1 - C a * X).prod := by
  rw [charpolyRev_def, ← reverse_multiset_prod_X_sub_C, ← charpoly_eq_prod_roots]

theorem card_roots_charpoly (f : V →ₗ[K] V) : f.charpoly.roots.card = finrank K V := by
  rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), charpoly_natDegree]

theorem det_eq_prod_roots_charpoly (f : V →ₗ[K] V) : f.det = f.charpoly.roots.prod := by
  classical
  set b := Module.finBasis K V with hb
  rw [← det_toMatrix b, ← charpoly_toMatrix f b, Matrix.det_eq_prod_roots_charpoly]

theorem zero_notMem_roots_charpoly {f : V →ₗ[K] V} (hf : IsUnit f.det) :
    (0 : K) ∉ f.charpoly.roots := fun h ↦ by
  rw [det_eq_prod_roots_charpoly, Multiset.prod_eq_zero h] at hf
  exact not_isUnit_zero hf

end LinearMap
