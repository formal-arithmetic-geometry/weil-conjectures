/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.TateAbstractResidueCalculus
import Sheaf.RingTheory.TateResidue.FinitePotentTraceCalculus
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Kaehler.Basic

/-! # Additivity of Tate residues in exact sequences

Source: J. Tate, *Residues of differentials on curves*, §1, (T2), p. 150,
and §2, Theorem 1 and its projection formula, pp. 151–152
(blueprint: lem-pc-tate-residue-exact-sequence).

The inherited subspaces are admissible, and the residue of the middle module is
the sum of the residues of the two end modules. The admissibility predicate and
residue maps are the existing `TateResidue.Admissible` and `TateResidue.res`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w₁ w w₃

namespace TateResidue

/-- Admissibility and additivity for a short exact sequence of modules over a
commutative algebra over a field.

Source: Tate, *Residues of differentials on curves*, §1, (T2), p. 150,
and §2, Theorem 1 and its projection formula, pp. 151–152
(blueprint: lem-pc-tate-residue-exact-sequence).

Proof plan:
1. Put N = im(i) = ker(q), I = A ∩ N, and let p : V → V/N be the quotient.
   For each r, (rI + I)/I injects into (rA + A)/A, and
   (r p(A) + p(A))/p(A) is a quotient of (rA + A)/A. These spaces are finite
   dimensional by `lem-pc-tate-abstract-residue-calculus`. The R-linear
   isomorphisms V₁ ≃ N and V/N ≃ V₃ carry the inherited subspaces to I and
   p(A), proving both admissibility conclusions.
2. By `lem-trf-vector-subspace-complement`, choose A = I ⊕ B, N = I ⊕ C,
   and V = (A + N) ⊕ D. Then V = I ⊕ B ⊕ C ⊕ D. Projection onto I ⊕ B
   fixes A and preserves N; it restricts to projection onto I in N and
   descends to projection onto p(A) in V/N. No R-linear splitting is required.
3. For f,g in R, the commutator T = [π m_f, m_g] preserves N. Its restriction
   and quotient are the commutators of the induced projections with the
   corresponding multiplication operators. The projection formula in
   `lem-pc-tate-abstract-residue-calculus` identifies their finite-potent traces
   with the three residues on f dg.
4. Apply stable-subspace trace additivity from
   `lem-pc-finite-potent-trace-calculus` to N and T. Transport the resulting
   identity through V₁ ≃ N and V/N ≃ V₃ using invariance of the residue under
   R-linear isomorphisms of pairs from `lem-pc-tate-abstract-residue-calculus`.
5. Every differential is a finite sum of f dg, by
   `def-weil-pbc-kahler-differentials`. All three residues are k-linear, so the
   identity on these generators gives equality of the maps on Ω¹(R/k).
-/
theorem admissible_and_res_eq_add_of_exact
    {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R]
    {V₁ : Type w₁} [AddCommGroup V₁] [Module k V₁] [Module R V₁]
    [IsScalarTower k R V₁]
    {V : Type w} [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
    {V₃ : Type w₃} [AddCommGroup V₃] [Module k V₃] [Module R V₃]
    [IsScalarTower k R V₃]
    (i : V₁ →ₗ[R] V) (q : V →ₗ[R] V₃)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hex : Function.Exact i q)
    (A : Submodule k V) (hA : Admissible R A) :
    Admissible R (A.comap (i.restrictScalars k)) ∧
    Admissible R (A.map (q.restrictScalars k)) ∧
    res R A = res R (A.comap (i.restrictScalars k)) +
      res R (A.map (q.restrictScalars k)) := by
  sorry

end TateResidue
