/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Sheaf.CategoryTheory.LeftDerivedValueMorphism
import Sheaf.CategoryTheory.DerivedFunctorShift

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- Intermediate obligation from the Lemma 05SC value-triangle construction.

Proof: this is the corresponding distinguished-triangle (respectively shifted
cone-equation) part of the construction in Stacks Project, Derived Categories,
Lemma 05SC; the remaining categorical argument is intentionally split for a
subsequent worker.
(blueprint: lem-pur-derived-functor-triangles-05sc-value-triangle-compatibility) -/
theorem leftDerived_value_triangle_extension_compat
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
    (T : Triangle C) (hT : T ∈ distTriang C)
    (LX LY LZ : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (hZ : F.IsTriangulatedLeftDerivedValue S hS T.obj₃ LZ)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
    (uZ : (Functor.const (S.Over ⊤ T.obj₃)).obj LZ ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ T.obj₁, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ T.obj₁, ∃ t : S.Over ⊤ T.obj₁,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (huY : ∃ s₀ : S.Over ⊤ T.obj₂, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ T.obj₂, ∃ t : S.Over ⊤ T.obj₂,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uY.app s)
    (huZ : ∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ LZ,
      uZ.app s₀ ≫ r = 𝟙 LZ ∧
        ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uZ.app s)
    (lf : LX ⟶ LY) (lg : LY ⟶ LZ)
    (hf : ∀ (s : S.Over ⊤ T.obj₁) (s' : S.Over ⊤ T.obj₂)
        (f' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₁ = f' ≫ s'.hom →
          uX.app s ≫ F.map f' = lf ≫ uY.app s')
    (hg : ∀ (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
        (g' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₂ = g' ≫ s'.hom →
          uY.app s ≫ F.map g' = lg ≫ uZ.app s')
    (lh : LZ ⟶ (shiftFunctor D (1 : ℤ)).obj LX)
    (hdist : Triangle.mk lf lg lh ∈ distTriang D) :
      ∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
        (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left),
        s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom →
          uZ.app s ≫ F.map h' =
            lh ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
              (F.commShiftIso (1 : ℤ)).inv.app s'.left := by
  sorry


end CategoryTheory.Functor
