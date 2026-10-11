/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H1
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The fixed-exponent monomial Cech complex

Source: Stacks Project, Cohomology of Schemes, Tag 01XS, proof of projective-space
cohomology (blueprint: def-pc-exponent-cech-complex).
-/

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

variable {A : Type*} [CommRing A]

/-- The set of coordinates where the fixed exponent vector is negative.
Source: Stacks, Tag 01XS (blueprint: def-pc-exponent-cech-complex). -/
def exponentCechNegativeSet (n : ℕ) (e : Fin (n + 1) → ℤ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => e i < 0

/-- The subsets indexing degree `p` for a fixed exponent vector.
Source: Stacks, Tag 01XS (blueprint: def-pc-exponent-cech-complex). -/
def exponentCechBasis (n : ℕ) (e : Fin (n + 1) → ℤ) (p : ℕ) :=
  {J : Finset (Fin (n + 1)) // J.card = p + 1 ∧
    exponentCechNegativeSet n e ⊆ J}

/-- The degree-`p` differential on the subset basis, adding one vertex with its alternating
sign. Source: Stacks, Tag 01XS (blueprint: def-pc-exponent-cech-complex). -/
noncomputable def exponentCechDifferential (n : ℕ) (e : Fin (n + 1) → ℤ) (p : ℕ) :
    (exponentCechBasis n e p →₀ A) →ₗ[A]
      (exponentCechBasis n e (p + 1) →₀ A) :=
  Finsupp.linearCombination A fun J =>
    ∑ k : Fin (n + 1),
      if hk : k ∉ J.1 then
        (((-1 : A) ^ (J.1.filter fun j => j < k).card) •
          Finsupp.single
            (⟨insert k J.1,
              ⟨by simp [Finset.card_insert_of_notMem hk, J.2.1],
               Finset.Subset.trans J.2.2 (Finset.subset_insert _ _)⟩⟩ :
              exponentCechBasis n e (p + 1)) (1 : A))
      else 0

/-- Two consecutive alternating differentials compose to zero. Pair the two orders of
inserting distinct vertices; their signs are opposite. Source: Stacks, Tag 01XS
(blueprint: def-pc-exponent-cech-complex). -/
theorem exponentCechDifferential_comp (n : ℕ) (e : Fin (n + 1) → ℤ) (p : ℕ) :
    exponentCechDifferential (A := A) n e (p + 1) ∘ₗ
      exponentCechDifferential (A := A) n e p = 0 := by
  sorry

/-- The fixed-exponent subcomplex of the alternating Cech complex: its degree-`p` term is
free on the subsets `J` of size `p+1` containing every negative coordinate of `e`.
Source: Stacks, Tag 01XS (blueprint: def-pc-exponent-cech-complex). -/
noncomputable def exponentCechComplex (n : ℕ) (e : Fin (n + 1) → ℤ) :
    CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of A (exponentCechBasis n e p →₀ A))
    (fun p => ModuleCat.ofHom (exponentCechDifferential (A := A) n e p))
    (fun p => by
      apply ModuleCat.hom_ext
      exact exponentCechDifferential_comp (A := A) n e p)

end AlgebraicGeometry.ProjectiveSpace
