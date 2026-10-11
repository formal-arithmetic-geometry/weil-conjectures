/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Idempotents

/-!
# Quotients of strictly henselian local rings

Source: Stacks Project, Algebra, Tag 05WS, specialized to a strictly henselian ring;
Tags 04GF and 09XI (3) (blueprint: lem-weil-pbc-strictly-henselian-quotient).
-/

@[expose] public section

universe u v

/-- A quotient by an ideal contained in the maximal ideal of a strictly henselian local
ring is local with the image maximal ideal and the same residue field, and is strictly
henselian, with unique idempotent lifting in every finite algebra.
Source: Stacks Project, Algebra, Tag 05WS and the idempotent criterion of Tag 09XI (3)
(blueprint: lem-weil-pbc-strictly-henselian-quotient).

Proof:
1. Since `I ≤ m`, `I` is proper. The quotient is local with maximal ideal `m/I`
   (`lem-weil-pbc-quotient-local-structure`).
2. The third isomorphism theorem identifies its residue field with `A/m`, compatibly
   with reduction from `A` (`lem-weil-pbc-quotient-residue-field`).
3. Any finite `A/I`-algebra is finite over `A`, and extension of `m` is extension of
   `m/I`. The henselian idempotent criterion therefore gives the unique lifts
   (`lem-weil-pbc-quotient-henselian-pair`, `def-weil-pbc-henselian-terminology`).
4. This proves henselianity; the residue-field identification transfers separable
   closedness, hence strict henselianity (`def-weil-pbc-henselian-terminology`). -/
theorem isStrictlyHenselianLocalRing_quotient
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hA : IsStrictlyHenselianLocalRing A) (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A) :
    ∃ (_ : IsLocalRing (A ⧸ I)),
      IsLocalRing.maximalIdeal (A ⧸ I) =
        (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) ∧
      (∃ e : IsLocalRing.ResidueField (A ⧸ I) ≃+* IsLocalRing.ResidueField A,
        ∀ a : A, e (IsLocalRing.residue (A ⧸ I) (Ideal.Quotient.mk I a)) =
          IsLocalRing.residue A a) ∧
      IsStrictlyHenselianLocalRing (A ⧸ I) ∧
      IsSepClosed (IsLocalRing.ResidueField A) ∧
      ∀ (B : Type (max u v)) [CommRing B] [Algebra (A ⧸ I) B] [Module.Finite (A ⧸ I) B],
        ∀ e : B ⧸ (IsLocalRing.maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) B),
          IsIdempotentElem e →
            ∃! b : B, IsIdempotentElem b ∧
              Ideal.Quotient.mk
                ((IsLocalRing.maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) B)) b = e := by
  sorry
