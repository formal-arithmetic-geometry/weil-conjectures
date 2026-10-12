/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.GroupTheory.PGroup
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Primary decomposition of finite discrete representations

Source: blueprint `lem-sc-affine-generic-second`, proof paragraph 1.
(blueprint: lem-sc-finite-discrete-rep-primary-decomposition)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace Rep

/-- A finite discrete continuous integral representation splits into finite primary
representations equivariantly.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraph 1.

Proof: take the exponent n of the finite abelian group underlying M. If n = 1, M is
zero and the empty family works. Otherwise enumerate the prime divisors p_i of n, and
put q_i = p_i ^ v_i(n). The subgroup killed by q_i is invariant under all integral
linear automorphisms. Give it the restricted action; its stabilizers are the same open
stabilizers as in M, so it defines a discrete continuous representation N_i. The subgroup
is finite and p_i-primary. Chinese remainder gives integers c_i equal to 1 modulo q_i
and 0 modulo the other q_j. Multiplication by c_i lands in N_i, commutes with the action,
and is its projection. Projection followed by inclusion is multiplication by c_i on M.
The sum of c_i is 1 modulo n, so the sum of the displayed composites is the identity.
(blueprint: lem-sc-finite-discrete-rep-primary-decomposition) -/
theorem exists_finite_primary_decomposition
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, v} ℤ G) [Finite M.obj.V] :
    ∃ (r : ℕ) (p : Fin r → ℕ) (N : Fin r → DiscreteContinuousRep.{0, u, v} ℤ G),
      (∀ i, (p i).Prime) ∧ (∀ i, Finite (N i).obj.V) ∧
      (∀ i, IsPGroup (p i) (Multiplicative (N i).obj.V)) ∧
      ∃ (a : ∀ i, M ⟶ N i) (b : ∀ i, N i ⟶ M),
        ∑ i, a i ≫ b i = 𝟙 M := by sorry

end Rep
