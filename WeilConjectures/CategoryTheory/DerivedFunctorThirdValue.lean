/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion
import WeilConjectures.CategoryTheory.ThirdValueConstruction

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- The third vertex has a left-derived value when the first two do.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause. -/
theorem leftDerived_definedAt_third_of_first_two
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
    (hX : F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₁)
    (hY : F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₂) :
    F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₃ := by
  let : S.HasRightCalculusOfFractions := hS.1.1.2
  let : IsCofiltered (S.Over ⊤ T.obj₃) := by
    refine {
      nonempty := ⟨MorphismProperty.Over.mk (P := S) ⊤ (𝟙 T.obj₃) (S.id_mem _)⟩
      cone_objs := ?_
      cone_maps := ?_ }
    · intro a b
      obtain ⟨ψ, hψ⟩ :=
        (MorphismProperty.LeftFraction.mk a.hom b.hom b.prop).exists_rightFraction
      let q := MorphismProperty.Over.mk (P := S) ⊤ (ψ.s ≫ a.hom)
        (S.comp_mem _ _ ψ.hs a.prop)
      exact ⟨q, MorphismProperty.Over.homMk ψ.s,
        MorphismProperty.Over.homMk ψ.f hψ.symm, trivial⟩
    · intro a b f g
      obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
        f.left g.left b.hom b.prop (f.w.trans g.w.symm)
      let q := MorphismProperty.Over.mk (P := S) ⊤ (t ≫ a.hom)
        (S.comp_mem _ _ ht a.prop)
      exact ⟨q, MorphismProperty.Over.homMk t, MorphismProperty.Over.Hom.ext heq⟩
  obtain ⟨A, hA⟩ := hX
  obtain ⟨B, hB⟩ := hY
  obtain ⟨Y, s, r, hbij⟩ := thirdValue_core F S hS T hT A B hA hB
  exact ⟨Y, (homColimit_essentiallyConstantProDiagram
    (MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    Y s r hbij).1⟩

end CategoryTheory.Functor
