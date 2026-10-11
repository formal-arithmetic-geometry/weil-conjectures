/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Idempotents

/-!
# Idempotent lifting and simple-root lifting for local rings

Source: Stacks Project, Algebra, Tags 04GF and 04GG (1) iff (10), and More on Algebra,
Tags 09XE and 09XI (1) iff (3) (blueprint: lem-weil-pbc-henselian-local-root-lifting).
-/

universe u v

namespace IsLocalRing

/-- For a local ring, unique lifting of idempotents in every finite algebra modulo the
extended maximal ideal is equivalent to lifting simple residue-field roots of monic
polynomials. The left side spells out the idempotent formulation of
`def-weil-pbc-henselian-terminology`; the right side is the residue-field condition in
`HenselianLocalRing.TFAE`.
Source: Stacks Project, Algebra, Tags 04GF and 04GG, and More on Algebra, Tags 09XE and 09XI
(blueprint: lem-weil-pbc-henselian-local-root-lifting).

Proof:
1. Idempotent lifts are unique for every finite algebra B over a local ring R. For two
   lifts e and e', d = e - e' lies in mB and satisfies d^3 = d. The ideal mB lies in the
   Jacobson radical by lem-weil-pbc-finite-algebra-local-radical. Thus 1 - d^2 is a unit,
   and d(1 - d^2) = 0 forces d = 0.
2. Assume idempotents lift. For a monic f and a simple residue root a₀, write its reduction
   as (T - a₀)h₀, with h₀(a₀) nonzero. The Chinese remainder theorem splits the quotient
   by this reduction into the linear factor and its complement. The algebra S = R[T]/(f)
   is finite free and has this residue quotient by lem-weil-pbc-monic-quotient-free.
   Lift the idempotent selecting the linear factor. Its factor A = eS is a finite flat
   direct summand, hence free by lem-weil-pbc-finite-flat-local-free. Its residue algebra
   is κ, so its rank is one. Its unit e is a basis: its coefficient in any basis is a
   unit since e has nonzero residue. Hence the structure map R → A is an isomorphism.
   The image a of T under R[T] → S → A ≅ R satisfies f(a) = 0 and has residue a₀.
3. Assume simple roots lift. By lem-weil-pbc-root-lifting-etale-retraction, each étale
   algebra with a prime over m inducing an isomorphism of residue fields has a unique
   R-algebra retraction whose inverse image of m is that prime (Stacks 04GG (1) ⇒ (8)).
4. By lem-weil-pbc-etale-retraction-finite-product-local, these retractions imply that
   every finite algebra B is a finite product of local rings (Stacks 04GG (8) ⇒ (10)).
5. Each local factor Bᵢ is finite over R, so mBᵢ is contained in its maximal ideal by
   lem-weil-pbc-finite-algebra-local-radical. Thus Bᵢ/mBᵢ is nonzero and local. Reduction
   of the finite product is the product of these quotients. In a local ring an
   idempotent is zero or one, since one of e and 1 - e is a unit and e(1 - e) = 0.
   Every residue idempotent is therefore a zero/one vector and lifts by the same vector
   in the product B. Step 1 gives uniqueness. The empty product includes the zero algebra.
   This proves the converse and hence the equivalence. -/
theorem idempotent_lifting_iff_monic_simple_root_lifting
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B],
      ∀ e₀ : B ⧸ (maximalIdeal R).map (algebraMap R B),
        IsIdempotentElem e₀ →
          ∃! e : B, IsIdempotentElem e ∧
            Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) e = e₀) ↔
      (∀ f : Polynomial R, f.Monic → ∀ a₀ : ResidueField R,
        Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ f.derivative ≠ 0 →
          ∃ a : R, f.IsRoot a ∧ residue R a = a₀) := by
  sorry

end IsLocalRing
