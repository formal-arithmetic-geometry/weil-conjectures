/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Sheaf.RingTheory.AssociatedGradedRingStructure
import WeilConjectures.RingTheory.AssociatedGradedRing

/-!
# The associated graded algebra of a regular-sequence ideal

Source: Stacks Project, Algebra, Tags 00LN (part (1)), 061N and 061P
(blueprint: lem-pur-regular-sequence-graded-polynomial).

The canonical map is constructed by polynomial evaluation. Its being a graded algebra
isomorphism is expressed by bijectivity and an equivalence between homogeneity of a
polynomial and membership of its image in the corresponding direct-sum summand.
The basis clause uses the finite, unique expansion criterion of
`def-weil-pbc-free-module`, so it does not choose another scalar action on the pieces.
-/

@[expose] public section

universe u

namespace Ideal

/-- The canonical polynomial-to-associated-graded map of Stacks, Algebra, Tag 061N,
specialized to `M = R` (blueprint: lem-pur-regular-sequence-graded-polynomial).
It sends each variable to the degree-one class of the corresponding generator and
commutes with the quotient-ring structure maps, hence fixes constants in degree zero. -/
noncomputable def regularSequenceGradedPolynomialMap {R : Type u} [CommRing R]
    {c : ℕ} (f : Fin c → R) :
    MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f)) →ₐ[R ⧸ Ideal.span (Set.range f)]
      associatedGraded (Ideal.span (Set.range f)) :=
  MvPolynomial.aeval (fun j ↦
    DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) 1
      (Submodule.Quotient.mk
        (⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩ :
          (Ideal.span (Set.range f) ^ 1 : Ideal R))))

/-- A regular sequence has polynomial associated graded algebra, including the formula
on coefficient lifts and the monomial basis in each degree. Source: Stacks, Algebra,
Tags 00LN (part (1)), 061N and 061P
(blueprint: lem-pur-regular-sequence-graded-polynomial).

Proof (the thirteen steps of the node):
1. Use `lem-weil-pbc-associated-graded-ring-structure` for the quotient-algebra
   structure, degree-zero inclusion, product formula and scalar formula.
2. Polynomial evaluation gives the displayed canonical map. Multiplying homogeneous
   classes gives its monomial formula; additivity gives the finite-sum formula.
   Changing a coefficient lift by an element of the ideal changes the sum by an
   element of the next power, so the formula is independent of all coefficient lifts.
3. Expand products of generators to span every ideal power by monomials of that
   degree. Elements of the next power have degree-n expansions with coefficients in J.
4. Induct on the length, in all rings and degrees, to show that a degree-n relation
   modulo the next power has all coefficients in J. For the empty sequence, degree
   zero says the sole coefficient is zero and positive degrees have no monomials.
5. The prefix is regular and the last generator t acts injectively modulo its ideal K;
   repeated cancellation shows that t^l a in K implies a in K.
6. Subtract an expansion with coefficients in J to reduce to a zero relation. Group
   by powers of t and induct on the largest exponent l, with length and degree fixed.
7. At l = 0, apply the outer induction to the regular prefix in degree n.
8. At l > 0, put d = n-l. Lower-exponent terms lie in K^(d+1); the outer induction
   in degree d puts t^l times every top coefficient in K. Cancel t^l by step 5.
9. Expand these top coefficients in the prefix generators. Group terms indexed by
   beta plus a unit multi-index, and move one factor t into the coefficients of the
   exponent-(l-1) terms. This also works for an empty prefix, when the top term is zero.
10. The inner induction puts the modified coefficients in J. Subtract their added
    multiples of t, restore the coefficients subtracted in step 6, and finish both inductions.
11. Lift the coefficients of a homogeneous polynomial in the kernel; step 4 makes
    them zero modulo J. Step 3 supplies a preimage of every homogeneous class.
12. Decompose polynomials and direct-sum elements into finitely many homogeneous
    components. Degreewise injectivity and surjectivity give bijectivity and the
    asserted equivalence of degree conditions, also for the inverse.
13. Transport the unique finite monomial expansions of homogeneous polynomials by
    the degreewise bijection. These are exactly the stated basis expansions; at
    degree zero the basis is the singleton 1, and for an empty sequence in positive
    degree the basis is empty and the piece is zero. -/
theorem regularSequence_gradedPolynomial {R : Type u} [CommRing R]
    {c : ℕ} (f : Fin c → R) (hf : RingTheory.Sequence.IsRegular R (List.ofFn f)) :
    Function.Bijective (regularSequenceGradedPolynomialMap f) ∧
    (∀ (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f))),
      p.IsHomogeneous n ↔
        ∃ x : associatedGradedPiece (Ideal.span (Set.range f)) n,
          regularSequenceGradedPolynomialMap f p =
            DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n x) ∧
    (∀ (n : ℕ) (a : {α : Fin c →₀ ℕ // α.sum (fun _ k ↦ k) = n} →₀ R),
      ∃ x : (Ideal.span (Set.range f) ^ n : Ideal R),
        x.val = a.sum (fun α r ↦ r * α.val.prod (fun j k ↦ f j ^ k)) ∧
        regularSequenceGradedPolynomialMap f
            (a.sum (fun α r ↦
              MvPolynomial.monomial α.val (Ideal.Quotient.mk (Ideal.span (Set.range f)) r))) =
          DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n
            (Submodule.Quotient.mk x)) ∧
    (∀ (n : ℕ) (x : associatedGradedPiece (Ideal.span (Set.range f)) n),
      ∃! a : {α : Fin c →₀ ℕ // α.sum (fun _ k ↦ k) = n} →₀
          (R ⧸ Ideal.span (Set.range f)),
        a.sum (fun α b ↦ b • regularSequenceGradedPolynomialMap f
          (MvPolynomial.monomial α.val 1)) =
            DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n x) := by
  sorry

end Ideal
