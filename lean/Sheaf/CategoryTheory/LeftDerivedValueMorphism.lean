/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Morphisms between pointwise left-derived values

Source: Stacks Project, Derived Categories, Lemma 05SA(2)
(blueprint: lem-pur-derived-functor-morphisms-05sa).
-/

universe u v uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- In Situation 05S8, a morphism between objects where `LF` is defined induces a unique
morphism between its values, compatible with every denominator square. The supplied
natural transformations are the cone maps exhibiting these values as essentially
constant pro-objects: `huX` and `huY` are precisely the retraction and common-stage
conditions of `IsEssentiallyConstantProDiagram`, with its existential cone made explicit.
Source: Stacks Project, Derived Categories, Lemma 05SA(2)
(blueprint: lem-pur-derived-functor-morphisms-05sa).

Proof: (1) The bridge `lem-pur-left-derived-defined-pointwise-kan-bridge` supplies limit
cones over `(Q(X) ↓ Q)` and `(Q(Y) ↓ Q)`, whose denominator projections are the given
cone maps. (2) Precomposition with `Q(f)` sends `(Z', φ)` over `Q(Y)` to `(Z', Q(f) ≫ φ)`
over `Q(X)`. Restrict the first limit cone along this functor and use the second limit's
universal property to obtain the morphism between values.
(3) For a denominator square, the identity
`Q(f) ≫ inv (Q(s')) = inv (Q(s)) ≫ Q(f')` and cone naturality give the first square.
Applying `F` to the original square gives the second square, hence the outer rectangle.
(4) For uniqueness, `lem-pc-right-localization-hom-colimit` writes every structured-arrow
projection as a denominator projection followed by `F(g)`. MS2 completes `f` and that
denominator to a square. The required first-square equation makes both candidate maps
agree after every projection; the limit universal property then makes them equal. -/
theorem leftDerived_value_morphism
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C) (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    {X Y : C} (f : X ⟶ Y) (LX LY : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS X LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS Y LY)
    (uX : (Functor.const (S.Over ⊤ X)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)
    (uY : (Functor.const (S.Over ⊤ Y)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ X, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ X, ∃ t : S.Over ⊤ X, ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
          F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (huY : ∃ s₀ : S.Over ⊤ Y, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ Y, ∃ t : S.Over ⊤ Y, ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
          F.map b.left = F.map a.left ≫ r ≫ uY.app s) :
    ∃! lf : LX ⟶ LY,
      ∀ (s : S.Over ⊤ X) (s' : S.Over ⊤ Y) (f' : s.left ⟶ s'.left),
        s.hom ≫ f = f' ≫ s'.hom →
          uX.app s ≫ F.map f' = lf ≫ uY.app s' ∧
            (uX.app s ≫ F.map s.hom) ≫ F.map f =
              lf ≫ uY.app s' ≫ F.map s'.hom := by
  sorry

end CategoryTheory.Functor
