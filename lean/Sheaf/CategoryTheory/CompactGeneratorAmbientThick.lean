/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-! # Compact objects lie in the ambient thick envelope of a compact generator

Source: Stacks Project, Tags 09SN, 09SP and 094A.
(blueprint: lem-sc-compact-generator-ambient-thick).
-/

@[expose] public section

universe u v w

open CategoryTheory.Limits

namespace CategoryTheory

set_option linter.unusedVariables false in
/-- A compact object presented by a generator telescope lies in its ambient thick envelope.
Source: Stacks Project, Tags 09SP (lemma-factor-through) and 094A
(lemma-commutes-with-countable-direct-sums), applied to the tower of 09SN.
(blueprint: lem-sc-compact-generator-ambient-thick).

Proof: Lift the supplied tower to A.FullSubcategory. Each attaching coproduct belongs to A by
the triangle and the two adjacent tower terms; the final sum belongs to A by closure under
universe-w coproducts after reindexing its countable family. Their ambient colimit universal
properties restrict to the full subcategory. The inclusion respects shifts and distinguished
triangles. Reindex the countable coproduct by ULift ℕ in universe w. By 094A, compact Hom
commutes with the sequential homotopy colimit, so the identity of P factors through a finite
stage. If this stage is zero, the identity of P factors through zero, hence P is zero.
Otherwise use the tail starting at X 1. Its initial term is isomorphic to B 0 because X 0 is
zero. For each later transition, inverse rotation gives the attaching term B n[-1]; shifting
a colimiting cofan by the shift equivalence gives a coproduct of the corresponding shifts
of G. These are the initial-term and transition hypotheses of 09SP. Apply 09SP to the
map from P into the selected stage. It factors through an object in the thick envelope of a
finite sum of copies of G. Finite sums of G lie in its singleton envelope, and the composite
back to P is its identity. Thus P is a retract of an object in that envelope. The inclusion
preserves shifts, finite sums, triangles and retract equations, so this internal construction
lies in the ambient singleton envelope. Retract closure gives the claim. No coproduct larger
than universe w is used and no infinite coproduct is required to be preserved by the inclusion
beyond those explicitly supplied. The zero initial stage or an empty attaching sum gives a zero
factorization; the zero object lies in the envelope of G even when G is zero. -/
theorem compact_generator_ambient_thick
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [HasCoproducts.{w} A.FullSubcategory]
    [∀ I : Type w, A.IsClosedUnderColimitsOfShape (Discrete I)]
    (G : A.FullSubcategory) (hG : IsCompactObject G)
    (P : A.FullSubcategory) (hP : IsCompactObject P)
    (X : ℕ → A.FullSubcategory) (t : ∀ n : ℕ, (X n).obj ⟶ (X (n + 1)).obj)
    (hzero : IsZero (X 0).obj)
    (hsteps : ∀ n : ℕ, ∃ (I : Type w) (m : I → ℤ)
      (B : Cofan (fun i : I ↦ G.obj⟦m i⟧)), Nonempty (IsColimit B) ∧
      ∃ (a : (X (n + 1)).obj ⟶ B.pt) (b : B.pt ⟶ (X n).obj⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk (t n) a b ∈ distTriang C)
    (S : Cofan (fun n : ℕ ↦ (X n).obj)) (hS : IsColimit S)
    (s : S.pt ⟶ S.pt) (q : S.pt ⟶ P.obj) (r : P.obj ⟶ S.pt⟦(1 : ℤ)⟧)
    (hs : ∀ n : ℕ, S.inj n ≫ s = t n ≫ S.inj (n + 1))
    (hT : Pretriangulated.Triangle.mk (𝟙 S.pt - s) q r ∈ distTriang C) :
    (ObjectProperty.singleton G.obj).triangEnvelope P.obj := by sorry

end CategoryTheory
