/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Cancelling a residue-exact degree of a finite free complex

Source: Stacks Project, More on Algebra, Tag 068U, `lemma-cut-complex-in-two`,
the direct matrix proof.
(blueprint: lem-weil-pbc-free-complex-residue-degree-cancellation)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A residue-exact degree can be removed after one principal localization.

Source: Stacks Project, More on Algebra, Tag 068U, `lemma-cut-complex-in-two`,
the direct matrix proof.
(blueprint: lem-weil-pbc-free-complex-residue-degree-cancellation)

Proof: Choose finite bases in degrees i-1, i, i+1 and induct on the size of the
middle basis, uniformly in rings, primes and complexes. If that size is zero,
take f=1 and the identity homotopy equivalence. Otherwise residue exactness
forces a nonzero entry in one of the adjacent differential matrices. Invert its
lift a outside the prime. The prime extended to R_a has the same residue field:
its quotient embeds in Frac(R/p), and every fraction is a quotient of images.
The scalar-extension reassociation maps on pure tensors identify the residue
complexes. Permute and rescale bases and subtract multiples of the pivot row
and column to put the chosen differential in the form diag(1,D). The equations
d squared equals zero isolate the identity block as a two-term subcomplex.
Projection and inclusion split off this block; its contracting homotopy sends
its target basis vector to its source basis vector and is zero elsewhere.
Tensoring these homotopy identities with the residue field preserves cohomology,
so induction applies to the complementary complex, whose middle rank dropped
by one. A further localization at g=b/a^t, outside the extended prime, combines
with the first as (R_a)_g = R_(ab), with ab outside p. Reassociate tensor products
termwise and transport maps and homotopies through this identification. Compose
the equivalences: if p1,q1,h1 describe the first contraction and p2,q2,h2 the
second, the resulting homotopy is h1+q1 h2 p1; the opposite composite has the
second homotopy since p1 q1=1. Outside the three indicated degrees the operations
are identities. The adjacent complementary finite free spans are split summands
of the original terms, since successive direct-sum decompositions compose.
Every original zero term remains zero. This proves all clauses without a bound
on the support of the complex. -/
theorem exists_localized_homotopyEquiv_zero_degree
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (i : ℤ)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hfree : ∀ j : ℤ, Module.Free R (P.X j))
    (hfinite : ∀ j : ℤ, Module.Finite R (P.X j))
    (hresidue : IsZero
      (((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars.{u, u, max u v}
          ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)))
        (ComplexShape.up ℤ)).obj P).homology i)) :
    ∃ (f : R), f ∉ p ∧
      ∃ (Q : CochainComplex (ModuleCat.{max u v} (Localization.Away f)) ℤ),
        (∀ j : ℤ, Module.Free (Localization.Away f) (Q.X j)) ∧
        (∀ j : ℤ, Module.Finite (Localization.Away f) (Q.X j)) ∧
        Nonempty (HomotopyEquiv
          ((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f)))
            (ComplexShape.up ℤ)).obj P) Q) ∧
        IsZero (Q.X i) ∧
        (∀ j : ℤ, j ∉ ({i - 1, i, i + 1} : Set ℤ) →
          Q.X j = (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f))).obj
            (P.X j)) ∧
        (∀ j k : ℤ, j ∉ ({i - 1, i, i + 1} : Set ℤ) →
          k ∉ ({i - 1, i, i + 1} : Set ℤ) →
          HEq (Q.d j k)
            ((ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f))).map
              (P.d j k))) ∧
        (∀ j : ℤ, j = i - 1 ∨ j = i + 1 →
          ∃ (a : Q.X j ⟶
              (ModuleCat.extendScalars.{u, u, max u v}
                (algebraMap R (Localization.Away f))).obj (P.X j))
            (b : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f))).obj
              (P.X j) ⟶ Q.X j), a ≫ b = 𝟙 (Q.X j)) ∧
        (∀ j : ℤ, IsZero (P.X j) → IsZero (Q.X j)) := by
  sorry

end CochainComplex
