/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective

/-! # Cancelling the degree-zero complement of universal rank-one homology

Source: Stacks Project, Tags 0BCC and 00O0, fixed-affine adaptation.
(blueprint: lem-sc-connective-universal-h0-zero-differential).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- For a connective finite projective complex, universally rank-one zeroth homology
permits cancellation of the complementary degree-zero summand.

Source: Stacks Project, Tags 0BCC and 00O0; degree-zero part of the fixed-affine
normalization argument in lem-sc-universal-h0-projective-normalization.
(blueprint: lem-sc-connective-universal-h0-zero-differential).

Proof: At a prime localize P over A = R_p. Finite projective modules over this
local ring are finite free. Tag 0BCC represents this perfect complex by a finite
free minimal model with ranks equal to its residue homology dimensions. The
ranks vanish outside the finite support bounds, so this model is bounded.
Its negative ranks are zero
because a connective complex remains connective under termwise scalar extension.
Its degree-zero rank is one by the residue test of hzero. Bounded projective
models of the same derived object are homotopy equivalent, and this comparison
remains a homotopy equivalence under any scalar extension. The test
of hzero on A identifies the kernel of the model's differential A -> A^m with A.
Its inclusion into A is multiplication by a non-zero-divisor c. The equation
d(c)=0 forces every coordinate of d(1) to vanish; hence d=0, with no reducedness
assumption. On this model the canonical H0 base-change map to each residue field
is an isomorphism. Transport through the homotopy comparisons shows the same
for the localization of P. Exact localization identifies its H0 with the
localization of H0(P), so the global cycle inclusion has injective reduction
at this prime. The identity test of hzero gives H0(P) isomorphic to R. Since P^(-1)=0,
its canonical cycle inclusion gives j:R -> P^0; its residue extension is
injective at every prime by the base-change comparison. Tag 00O0, finite
presentation, and local-to-global projectivity show that coker(j) is finite
projective and j splits globally. Write P^0 = R plus E using this splitting.
The differential vanishes on R, and its restriction E -> P^1 is injective
at every residue field because the residue kernel is exactly the R summand.
Again Tag 00O0 makes this restriction a split injection with finite projective
cokernel. Cancel the pair E -> image(E) in degrees zero and one using its
inverse as contracting homotopy. The remaining complex has term R in degree
zero, zero outgoing differential, its degree-one term is that cokernel, and
higher terms unchanged. It is bounded, finite projective, and connective.
Projection and inclusion exhibit the homotopy equivalence. Over the zero ring
P itself already has zero differentials. The argument also allows zero higher
terms, including a complex supported only in degree zero. -/
theorem connective_universalH0_zero_differential
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite R (P.X n))
    (hp : ∀ n : ℤ, Module.Projective R (P.X n))
    (hconnective : ∀ n : ℤ, n < 0 → IsZero (P.X n))
    (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∃ Q : CochainComplex (ModuleCat.{v} R) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Q.X n)) ∧
      (∀ n : ℤ, Module.Finite R (Q.X n)) ∧
      (∀ n : ℤ, Module.Projective R (Q.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (Q.X n)) ∧
      Q.d 0 1 = 0 ∧ Nonempty (HomotopyEquiv P Q) := by sorry

end CochainComplex
