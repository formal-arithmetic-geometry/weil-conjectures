/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra

import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels

/-! # Completed free presentations for adic towers

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

/-- A vector mapping to zero at one tower level can be corrected by a global
presentation-kernel vector with the same free residue at that level.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, proof, the surjection
K → K_n used in the final cokernel calculation.
(blueprint: lem-weil-pbc-adic-tower-free-kernel-correction).

Proof: Put P = A^d and P_n = P/I^(n+1)P. The map q followed by the nth
projection factors through P_n: identify the completed free module with a
finite product of the completed ring, choose representatives of each residue,
and use the completed scalar equation on each basis vector. Hence the projected
value depends only on the residue, and the factor is A-linear. The
tower projections are surjective by recursive lifting along htrans. Hence
q surjective makes each composite to T_n surjective, and its factor
P_n → T_n is surjective. The factors commute with transitions, as equality
can be tested on lifts to the completed free module. Let K_n be their kernels.
Lift a K_n vector to P_(n+1). Its image in T_(n+1) lies in I^(n+1)T_(n+1).
Surjectivity of P_(n+1) → T_(n+1) supplies an I^(n+1) correction vector;
subtracting it proves that K_(n+1) → K_n is surjective. Thus every K_n vector
lifts to a compatible kernel sequence. The identification of the free
completion with lim P_n makes that sequence a vector z. Every coordinate
of q(z) is zero, so limit extensionality and injectivity of e give q(z)=0.
Apply this to the residue of y, which lies in K_n by the given equation.
The resulting z has the same nth residue as y. No finite generation of T_n
or Noetherian hypothesis is used in this correction argument. -/
theorem adicTower_freeKernelCorrection (A : Type u) [CommRing A]
    (I : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hzero : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) = ⊥)
    (htrans : ∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I ^ (n + 1) • (⊤ : Submodule A (T.obj (op (n + 1)))))
    (N : ModuleCat.{u} (AdicCompletion I A))
    (e : (restrictScalars (algebraMap A (AdicCompletion I A))).obj N ≅ limit T)
    (hscalar : ∀ (n : ℕ) (r : AdicCompletion I A) (a : A) (x : N),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (e.hom ≫ limit.π T (op n)) (r • x) =
        a • (e.hom ≫ limit.π T (op n)) x)
    (d : ℕ) (q : AdicCompletion I (Fin d → A) →ₗ[AdicCompletion I A] N)
    (hq : Function.Surjective q) (n : ℕ) (y : AdicCompletion I (Fin d → A))
    (hy : (e.hom ≫ limit.π T (op n)) (q y) = 0) :
    ∃ z : AdicCompletion I (Fin d → A), q z = 0 ∧
      AdicCompletion.eval I (Fin d → A) (n + 1) z =
        AdicCompletion.eval I (Fin d → A) (n + 1) y := by sorry

end ModuleCat
