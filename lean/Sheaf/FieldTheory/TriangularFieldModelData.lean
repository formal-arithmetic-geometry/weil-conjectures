/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Triangular relations from an algebraic tower

Source: Stacks Project, Algebra, proof of Tag 07BV and Tag 08JZ.
-/

@[expose] public section

universe u v

namespace FieldTheory

/-- Construct triangular minimal-polynomial relations and independent bounded products.
Source: Stacks Project, Algebra, proof of Tag 07BV, first assertion
(blueprint: lem-weil-pbc-triangular-field-model-data).

Proof: Put F = k(x) and L_i = F(b_j : j < i). The transcendence-basis
hypothesis makes all b_i algebraic over F. Take their minimal polynomials over
L_i. Their positive degrees e_i and the simple-extension power bases, multiplied
using Basis.smulTower, make the bounded products of the b_i an F-basis of L_m,
hence linearly independent in K. Expand each coefficient in the preceding product
basis. Replace the preceding generators by polynomial variables. Clear the finite
set of F-coefficient denominators by a single nonzero product h in k[X]. Lift a/h^n
to a(X) T^n and lift the leading coefficient as one. This gives monic p_i of
natDegree e_i. Evaluate the variables at x, h(x) inverse, and b. Algebraic
independence makes h(x) nonzero; thus the localization equation evaluates to zero,
and each lifted p_i evaluates to its minimal polynomial at b_i, also zero.
For m = 0 choose h = 1; the empty product is one and is F-independent. For d = 0,
F is k. Repeated generators give linear minimal polynomials and inseparability
requires no change. This construction asserts no kernel equality. -/
theorem exists_triangularFieldModel_data
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (d : ℕ) (x : Fin d → K) (hx : IsTranscendenceBasis k x)
    (m : ℕ) (b : Fin m → K) :
    ∃ (h : MvPolynomial (Fin d) k)
      (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
      (y : Fin (d + 1 + m) → K) (e : Fin m → ℕ),
      h ≠ 0 ∧ (∀ i, (p i).Monic) ∧ (∀ i, (p i).natDegree = e i) ∧
      (∀ j : Fin d, y ⟨j.val, by omega⟩ = x j) ∧
      y ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹ ∧
      (∀ i : Fin m, y ⟨d + 1 + i.val, by omega⟩ = b i) ∧
      (∀ q ∈ triangularFieldModelEquations k d m h p, MvPolynomial.aeval y q = 0) ∧
      LinearIndependent (IntermediateField.adjoin k (Set.range x))
        (fun a : ((i : Fin m) → Fin (e i)) => ∏ i, b i ^ (a i).val) := by sorry

end FieldTheory
