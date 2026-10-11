/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite homogeneous generators of a graded module

Source: Weil conjectures blueprint, `sec-picard-framework/sk-thm-picard-duality`,
proof, construction of the initial graded free module from homogeneous generators
(blueprint: lem-sc-p1-finite-homogeneous-generators).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- Every finitely generated graded module over `k[x₀,x₁]` has finitely many homogeneous
    generators, and these generators give a surjective graded map from a finite sum of shifts.

Source: blueprint `lem-sc-p1-graded-resolution.md`, proof, construction of the initial graded
free module from homogeneous generators (blueprint: lem-sc-p1-finite-homogeneous-generators).

Proof: choose ordinary module generators and decompose each into finitely many homogeneous
components. Their finite union is homogeneous and still generates. The shifted summands map by
multiplication by the corresponding generators; the grading convention is the shift convention
of `def-weil-pbc-proj-twisting-sheaf` (2). The zero module is covered by the empty family.
-/
theorem exists_finite_homogeneous_generators {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j →
        s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (r : ℕ) (d : Fin r → ℤ) (m : Fin r → M)
      (hm : ∀ i, m i ∈ ℳ (d i))
      (f : (Fin r →₀ MvPolynomial (Fin 2) k) →ₗ[MvPolynomial (Fin 2) k] M),
      Function.Surjective f ∧
      (∀ i, f (Finsupp.single i 1) = m i) ∧
      (∀ (i : Fin r) (n : ℕ) (s : MvPolynomial (Fin 2) k),
        s ∈ homogeneousSubmodule (Fin 2) k n →
          f (s • Finsupp.single i 1) ∈ ℳ ((n : ℤ) + d i)) := by
  sorry

end MvPolynomial
