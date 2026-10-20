/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
import Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.PerfectComplex

/-! # Derived scalar extension preserves perfect complexes

Source: Stacks Project, More on Algebra, Lemma 15.76.9, Tag 066W
(blueprint: lem-sc-perfect-pullback-perfect-residue).
-/

@[expose] public section

universe wA wB u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Derived scalar extension along any homomorphism of commutative rings preserves
perfect complexes. Perfectness over a ring (`def-pc-perfect-ring-complex`) is stated by the
bounded model with finitely generated projective terms (coord/STATE.md, PERFECT COMPLEXES;
the library predicate `DerivedCategory.IsPerfect` is bridged at stage 3). The chosen
fixed-second-factor derived tensor functor is evaluated at the regular `B`-module in degree
zero, so its value is `K ⊗ᴸ_A B` in `D(B)`.
Source: Stacks Project, More on Algebra, Lemma 15.76.9, Tag 066W
(blueprint: lem-sc-perfect-pullback-perfect-residue).

Proof:
1. By `lem-pc-perfect-affine-bounded-projective` (Tags 08EB and 0656), represent `K`
   by a bounded complex `P` of finite projective `A`-modules. Projective terms have
   no higher Tor with `B`. By `lem-pc-termwise-tor-acyclic-derived-tensor`, the
   derived scalar extension is represented by the termwise tensor complex `P ⊗_A B`.
2. Each term of `P` is a direct summand of a finite free `A`-module. Tensoring the
   splitting with `B` makes its scalar extension a direct summand of a finite free
   `B`-module, hence finite projective. Boundedness is preserved, so `P ⊗_A B` is a
   bounded model of finite projective `B`-modules. -/
theorem IsPerfect.scalarExtension {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (f : A →+* B) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite A (P.X n)) ∧
      (∀ n : ℤ, Module.Projective A (P.X n)) ∧
      Nonempty (Q.obj P ≅ K)) :
    ∃ P : CochainComplex (ModuleCat.{u} B) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite B (P.X n)) ∧
      (∀ n : ℤ, Module.Projective B (P.X n)) ∧
      Nonempty (Q.obj P ≅
        ((Classical.choose (exists_derivedTensor_second_factor_functor f).2).obj
          ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj
            (ModuleCat.of B B))).obj K) := by
  sorry

end DerivedCategory
