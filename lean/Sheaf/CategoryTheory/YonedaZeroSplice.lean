/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.CategoryTheory.YonedaDerivedExtComparison

/-! # Right splices and zero Yoneda extensions

Source: Stacks Project, Derived Categories, Tags 06XT and 06XP, the Yoneda
composition paragraph following Tag 06XV (blueprint: lem-coef-yoneda-zero-splice).

The exact sequences and endpoint-fixed zigzags are the existing `YonedaExtension`
and `YonedaExtension.Equivalent`. `RightSplice` specifies the splice on the right,
keeping the entire prefix and composing its last arrow with the short exact
sequence's inclusion. `IsStandardZero` describes the specified zero sequences up
to endpoint-fixed isomorphism: a split sequence in degree one, and identity end
arrows with zero middle arrows and intervening zero objects in higher degrees.
No derived Ext comparison, or projective or injective object, is assumed.
-/

@[expose] public section

universe u v

namespace CategoryTheory.YonedaExtension

open CategoryTheory.Limits

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The splice of an extension of `K` by `T` with `0 → K → P → F → 0`,
expressed by identifications of every retained term and all the specified arrows.
The isomorphism of prefixes retains all their differentials. The joining equation
composes the old final arrow with the given inclusion; the final equation uses
the given quotient map. Thus this is a concrete sequence specification, with no
arbitrary comparison morphism or derived-category product.

Source: Stacks Project, Derived Categories, Tag 06XP, composition after Tag 06XV
(blueprint: lem-coef-yoneda-zero-splice). -/
structure RightSplice {T : A} {n : ℕ} (S : ShortComplex A)
    (E : YonedaExtension A T S.X₁ (n + 1))
    (G : YonedaExtension A T S.X₃ (n + 2)) where
  /-- All prefix objects and arrows, omitting only the old quotient `K`. -/
  prefixIso : E.sequence.δlast ≅ G.sequence.δlast.δlast
  /-- Identification of the appended middle object `P`. -/
  lastIso : S.X₂ ≅ G.sequence.obj' (n + 2)
  /-- The retained prefix fixes `T`. -/
  left_comm : prefixIso.hom.app 0 ≫ G.leftIso.hom = E.leftIso.hom
  /-- The joining arrow is precisely `X₀ → K → P`. -/
  splice_comm : prefixIso.hom.app (Fin.last (n + 1)) ≫
      G.sequence.map' (n + 1) (n + 2) =
    E.sequence.map' (n + 1) (n + 2) ≫ E.rightIso.hom ≫ S.f ≫ lastIso.hom
  /-- The final arrow is precisely the quotient `P → F`. -/
  right_comm : lastIso.hom ≫ G.sequence.map' (n + 2) (n + 3) ≫ G.rightIso.hom = S.g

/-- The standard zero extension, specified up to endpoint-fixed isomorphism.
For degree one this is the existing splitting predicate, equivalently the sequence
`0 → V → V ⊕ U → U → 0` with its inclusion and projection. In degree `n + 2`,
the first and last arrows identify the first and last middle objects with `V` and
`U`; the `n` intervening objects are zero, and every middle arrow is zero.
This gives exactly the zero sequence in the node, including degree two with no
intervening zero objects.

Source: Stacks Project, Derived Categories, Tags 06XT and 06XP, explicit zero
representatives in the node (blueprint: lem-coef-yoneda-zero-splice). -/
def IsStandardZero {V U : A} {n : ℕ} (E : YonedaExtension A V U (n + 1)) : Prop :=
  match n, E with
  | 0, E => E.IsSplit
  | n + 1, E =>
    IsIso (E.sequence.map' 0 1) ∧ IsIso (E.sequence.map' (n + 2) (n + 3)) ∧
      (∀ (j : ℕ) (hj : 2 ≤ j) (hj' : j < n + 2), IsZero (E.sequence.obj' j)) ∧
      (∀ (j : ℕ) (hj : 1 ≤ j) (hj' : j < n + 2),
        E.sequence.map' j (j + 1) = 0)

/-- Splicing on the right exists, preserves endpoint-fixed Yoneda equivalence,
and takes a prefix equivalent to the specified zero extension to a sequence
 equivalent to the specified zero extension in the next degree. Zero models are
asserted to exist as part of the statement; the predicates do not add hypotheses
on the abelian category or replace the canonical splice by an arbitrary map.

Source: Stacks Project, Derived Categories, Tags 06XT and 06XP, composition after
Tag 06XV (blueprint: lem-coef-yoneda-zero-splice).

Proof plan (the node's six steps):
1. The split biproduct sequence is exact in degree one. In higher degrees the
identity end arrows and zero middle terms give exactness at every object.
2. Construct the splice with the retained prefix and appended `P`. Monicity of
`S.f` leaves the kernel at `X₀` unchanged, and epicity of the old final arrow
makes the image of the joining arrow equal to the image of `S.f`, hence the
kernel of `S.g`. All other exactness and endpoint conditions are unchanged.
3. Extend each endpoint-fixed prefix map by the identity on `P` and `F`.
The joining square commutes by composition with `S.f`. Apply this construction
to every arrow, in either orientation, of a generating zigzag.
4. In degree one map the splice of the split zero sequence to the zero
2-extension by the projection `T ⊕ K → T` and by `S.g : P → F`.
The squares are the biproduct identity, `S.f ≫ S.g = 0`, and the identity on `F`.
5. In larger degrees keep `T`, map the old last middle object `K` to zero,
and map `P` to `F` by `S.g`. All squares are zero except for the same relation
`S.f ≫ S.g = 0` and the identity end squares. This includes degree two of the
prefix, where it has no intervening zero object.
6. Splice the zigzag from the given prefix to its zero model, then append the
comparison from steps 4 or 5. Isomorphisms to any chosen standard zero models
fix the endpoints and can be appended to these zigzags.
No projective or injective objects and no derived Ext comparison are used. -/
theorem splice_equivalent_and_zero (S : ShortComplex A) (hS : S.ShortExact)
    (T : A) (n : ℕ) :
    (∃ Z : YonedaExtension A T S.X₁ (n + 1), Z.IsStandardZero) ∧
    (∃ Z : YonedaExtension A T S.X₃ (n + 2), Z.IsStandardZero) ∧
    (∀ E : YonedaExtension A T S.X₁ (n + 1),
      ∃ G : YonedaExtension A T S.X₃ (n + 2), Nonempty (RightSplice S E G)) ∧
    (∀ (E E' : YonedaExtension A T S.X₁ (n + 1))
      (G G' : YonedaExtension A T S.X₃ (n + 2)),
      RightSplice S E G → RightSplice S E' G' →
        E.Equivalent E' → G.Equivalent G') ∧
    (∀ (E Z : YonedaExtension A T S.X₁ (n + 1))
      (G W : YonedaExtension A T S.X₃ (n + 2)),
      RightSplice S E G → Z.IsStandardZero → W.IsStandardZero →
        E.Equivalent Z → G.Equivalent W) := by
  sorry

end CategoryTheory.YonedaExtension
