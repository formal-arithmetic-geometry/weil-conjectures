/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra

import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels
import Sheaf.RingTheory.NakayamaNilpotent

/-! # Completed free presentations for adic towers

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

/-- An adic tower admits a surjective completed finite free presentation.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, proof through the
short exact sequence with middle term the completed finite free module.
(blueprint: lem-weil-pbc-adic-tower-completed-free-surjection).

Proof: Choose generators of T_0 and lift them to the limit by recursive lifting
along the surjective transitions. Compose these lifts with e inverse. Their
images define compatible presentations at all levels from the quotients of
A^d by I^(n+1). Nilpotent Nakayama makes every presentation surjective: the
reduction is the chosen presentation of T_0. Indeed, inductively the composite
T_n → T_0 is surjective with kernel I T_n: lift an I-multiple through the
next surjective transition and use its kernel I^(n+1)T_(n+1) ⊆ I T_(n+1).
Thus T_n/I T_n identifies with T_0, while I^(n+1) kills T_n.
To lift a presentation kernel
vector one level, lift its coordinates arbitrarily. Its image is in
I^(n+1)T_(n+1) by the transition kernel assumption. Correct that image using
I^(n+1) times a vector in the surjective free presentation. This proves
surjectivity of the kernel transitions. Exactness of inverse limits for
surjective kernel transitions gives a surjection from the completion of A^d
to the limit. The completed scalar residue equation and equality detected by
all limit coordinates prove that its composite with e inverse is linear over
the completed ring. This yields the stated q. -/
theorem adicTower_completedFreeSurjection (A : Type u) [CommRing A]
    (I : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfinite : Module.Finite A (T.obj (op 0)))
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
        a • (e.hom ≫ limit.π T (op n)) x) :
    ∃ (d : ℕ) (q : AdicCompletion I (Fin d → A) →ₗ[AdicCompletion I A] N),
      Function.Surjective q := by sorry

end ModuleCat
