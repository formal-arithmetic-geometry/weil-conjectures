/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.LeftDerivedValueMorphism
import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Left derived values invert the multiplicative system

Source: Stacks Project, Derived Categories, Lemma 05SB(2)
(blueprint: lem-pur-derived-functor-inverts-05sb).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- In Situation 05S8, the left derived functor is defined at the two ends of every
morphism in the multiplicative system simultaneously, and its induced map is an isomorphism.

Source: Stacks Project, Derived Categories, Lemma 05SB(2)
(blueprint: lem-pur-derived-functor-inverts-05sb).

Proof: (1) Write `J_X = S/X` and `J_Y = S/Y`. For `s : X ⟶ Y` in `S`, MS1
of `def-pur-saturated-triangulated-localization` gives the postcomposition functor
`c : J_X ⥤ J_Y`, sending `u` to `u ≫ s`; restricting the `J_Y` pro-diagram along
`c` gives the `J_X` pro-diagram. The second MS2 clause gives, for every denominator
`t : Z ⟶ Y`, a denominator `u : W ⟶ X` and a map `v : W ⟶ Z` with
`u ≫ s = v ≫ t`, hence an arrow `c(u) ⟶ t`. For two such arrows, cofilteredness
of `J_X` gives a common source; the second MS3 clause applied to `t` then gives
an earlier denominator on which their maps to `Z` agree. Thus `c` is initial.
Stacks Categories Lemma 0A1T transfers essential constancy in both directions,
proving the iff of definedness.
(2) When both values exist, `lem-pur-derived-functor-morphisms-05sa`, rendered by
`leftDerived_value_morphism`, gives the unique compatible map `LF(s)`. For each
`Y' ⟶ Y` in `S`, the reverse MS2 comparison gives `X' ⟶ X` in `S` and a map
`X' ⟶ Y'` forming a denominator square. Applying `F` and the cone maps constructs
an inverse comparison `LF(Y) ⟶ LF(X)`. MS3 makes the construction independent
of the square. After a common refinement, MS3 makes both composites satisfy the
identity comparison equations. The uniqueness clause of 05SA(2) identifies them
with the two identity maps, so `LF(s)` is an isomorphism. -/
theorem leftDerived_inverts
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    {X Y : C} (s : X ⟶ Y) (hs : S s) :
    (F.IsTriangulatedLeftDerivedDefinedAt S hS X ↔
      F.IsTriangulatedLeftDerivedDefinedAt S hS Y) ∧
      (F.IsTriangulatedLeftDerivedDefinedAt S hS X →
        ∀ (LX LY : D),
          F.IsTriangulatedLeftDerivedValue S hS X LX →
          F.IsTriangulatedLeftDerivedValue S hS Y LY →
          ∀ (uX : (Functor.const (S.Over ⊤ X)).obj LX ⟶
              MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)
            (uY : (Functor.const (S.Over ⊤ Y)).obj LY ⟶
              MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F),
            (∃ s₀ : S.Over ⊤ X, ∃ r : F.obj s₀.left ⟶ LX,
              uX.app s₀ ≫ r = 𝟙 LX ∧
                ∀ t : S.Over ⊤ X, ∃ q : S.Over ⊤ X, ∃ a : q ⟶ s₀,
                  ∃ b : q ⟶ t, F.map b.left = F.map a.left ≫ r ≫ uX.app t) →
            (∃ s₀ : S.Over ⊤ Y, ∃ r : F.obj s₀.left ⟶ LY,
              uY.app s₀ ≫ r = 𝟙 LY ∧
                ∀ t : S.Over ⊤ Y, ∃ q : S.Over ⊤ Y, ∃ a : q ⟶ s₀,
                  ∃ b : q ⟶ t, F.map b.left = F.map a.left ≫ r ≫ uY.app t) →
            ∃ (lf : LX ⟶ LY),
              (∀ (a : S.Over ⊤ X) (b : S.Over ⊤ Y)
                  (f : a.left ⟶ b.left),
                  a.hom ≫ s = f ≫ b.hom →
                    uX.app a ≫ F.map f = lf ≫ uY.app b ∧
                      (uX.app a ≫ F.map a.hom) ≫ F.map s =
                        lf ≫ uY.app b ≫ F.map b.hom) ∧
                IsIso lf) := by
  sorry

end CategoryTheory.Functor
