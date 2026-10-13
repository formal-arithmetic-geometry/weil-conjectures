/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Sheaf.CategoryTheory.LeftDerivedValueMorphism
import Sheaf.CategoryTheory.DerivedFunctorShift
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion
import Sheaf.CategoryTheory.TriangleMorphismCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- A compatible third derived map can be chosen together with distinguishedness.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause (dual argument).

Proof: Complete lf by TR1 to (LX, LY, K, lf, b, c). Use MS2 and the common-stage
clauses of huX and huY to refine a denominator square for T.mor₁ until its
retractions alpha and beta satisfy F(f') beta = alpha lf. TR1 and MS6 extend
this square to a distinguished denominator triangle over T. TR3 extends alpha
and beta to a triangle morphism into the chosen completion, retaining its third
square. Over the cofiltered denominator-triangle category of 05R9, apply Hom(-, W)
and exact filtered colimits. The supplied value cones give bijections at the first
two vertices; at the shifted vertices use W[-1] and F's shift comparison. The five
lemma gives the third Hom-colimit bijection. Initiality of the vertex projections
and denominator change of base identify it with the full denominator diagram.
The essentially constant pro criterion 05PY and these representative equations
identify K with LZ by the unique isomorphism preserving the supplied third cone.
The second square and uniqueness in 05SA identify the transported b with lg.
Define lh by the inverse comparison followed by c. Refining any supplied h'
square to the triangle indexing category makes its cone equation the third square
of the comparison. Initiality, cone naturality and shift compatibility 05SU
therefore give the displayed equation for every h'. Transport distinguishedness
along the comparison isomorphism. It is essential to retain the third square:
an arbitrary distinguished completion need not satisfy the cone equation.
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
    : ∃ lh : LZ ⟶ (shiftFunctor D (1 : ℤ)).obj LX,
        Triangle.mk lf lg lh ∈ distTriang D ∧
        (∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
          (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left),
          s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom →
            uZ.app s ≫ F.map h' =
              lh ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
                (F.commShiftIso (1 : ℤ)).inv.app s'.left) := by
  sorry


end CategoryTheory.Functor
