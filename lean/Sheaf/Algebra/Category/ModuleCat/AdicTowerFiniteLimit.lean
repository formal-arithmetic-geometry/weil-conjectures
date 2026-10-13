/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Basic

import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels
import Sheaf.RingTheory.NakayamaNilpotent
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Finiteness and reduction of an adic tower limit

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

/-- Finite generation and the projection kernel formula for an algebraic adic tower.
This concerns one given completed module and one given limit comparison, and constructs
neither modules, functors nor morphism lifts.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, generator-lifting,
Nakayama, Mittag-Leffler and the final cokernel calculation.
(blueprint: lem-weil-pbc-adic-tower-finite-limit).

Proof: Surjectivity of successive transitions implies surjectivity of every limit
projection by recursive lifting. Lift a finite generating family at level zero to the
limit. At level n the resulting map from a finite free A/I^(n+1)-module is surjective:
its reduction modulo I generates level zero, and I/I^(n+1) is nilpotent, so apply
nilpotent Nakayama. The kernels of these free presentations have surjective transitions.
Indeed lift a kernel vector one level; its image is in I^(n+1) times the next module.
Surjectivity of the presentation supplies a correction vector in I^(n+1) times the
free module; subtract it without changing the preceding coordinate. The exactness
lemma for towers with surjective kernels now gives a surjection from a finite free
completed module onto the limit. The residue equation makes this surjection completed
linear, so N is finite. Fix n. An element in the kernel of the nth projection lifts
to the completed free module. Its nth coordinate lies in the presentation kernel;
lift this coordinate through the kernel tower and subtract the resulting kernel
sequence. The difference has zero nth coordinate in the completed free module, hence
lies in I^(n+1) times that free module by the completion quotient formula (the ideal
is finitely generated because A is Noetherian). Its image is the original element,
so it lies in I^(n+1)N. Conversely I^(n+1)N maps to zero by annihilation of the nth
term. This proves the kernel equality as an A-submodule. -/
theorem adicTower_finiteLimit (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfinite : ∀ n : ℕ, Module.Finite A (T.obj (op n)))
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
    Module.Finite (AdicCompletion I A) N ∧
    ∀ n : ℕ, Function.Surjective (e.hom ≫ limit.π T (op n)) ∧
      LinearMap.ker (e.hom ≫ limit.π T (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((restrictScalars (algebraMap A (AdicCompletion I A))).obj N)) := by sorry

end ModuleCat
