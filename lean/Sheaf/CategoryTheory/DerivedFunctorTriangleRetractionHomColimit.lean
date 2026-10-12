/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Yoneda

/-! # Five-lemma comparison for a triangle retraction

Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause (dual argument).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- A triangle retraction on the first two vertices induces a third Hom-colimit bijection.
Source: Stacks Project, Derived Categories, Lemma 05SC, the five-term Hom diagram,
dualized to LF; Categories, Tag 05PZ and the initial colimit comparison Tag 0A1T.
(blueprint: lem-pur-triangle-retraction-hom-colimit).

Proof: Let I be the cofiltered category of distinguished denominator triangles over U
in Tag 05R9. Its three vertex projections are initial. Compose its objects with sigma
and restrict the first two supplied cones along their vertex projections. Composition
with each sigma_i in S is initial by the fraction calculus (MS2 and MS3), so the
restricted diagrams are essentially constant with values LX and LY. Their cone
Hom-colimit maps are bijections by 05PZ. The chosen triangle U is the identity object
of I; rho supplies a comparison from the five-term Hom(-,W) sequence for (LX,LY,K)
to the filtered colimit of the sequences for the F-images of objects of I. At the
first two vertices the comparisons are inverse to the cone Hom-colimit maps:
the given retraction identities make each composite the identity. For the shifted
vertices use the shift equivalence with W[-1] and F's shift comparison; the same
retraction identities give the inverse comparisons there. Each F-image triangle
is distinguished, so its Hom sequence is exact. Filtered colimits of abelian groups
are exact. The squares of the comparison diagram commute because rho is a triangle
morphism. The five lemma therefore makes its middle comparison a bijection.
The third vertex projection is initial, as is denominator postcomposition with
sigma_3. Their opposites are final. Compose the canonical colimit bijections and
use their representative equations: the identity object of I goes to the denominator
sigma_3, and the middle comparison sends phi to the class of rho.hom3 followed by
phi. This is the stated function, for every W. This proof uses neither a third value,
a cone at K, nor any value-triangle completion theorem.

Edge cases: when rho is the identity comparison and S contains only isomorphisms,
the function is the ordinary canonical Hom-colimit bijection. Contractible and split
triangles satisfy the same exact-sequence argument. The retraction equations are
essential: merely supplying arbitrary maps at the first two vertices would be false. -/
theorem leftDerived_triangle_retraction_homColimit
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
    (LX LY : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
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
    (lf : LX ⟶ LY) (K : D) (b : LY ⟶ K)
    (c : K ⟶ (shiftFunctor D (1 : ℤ)).obj LX)
    (hK : Triangle.mk lf b c ∈ distTriang D)
    (U : Triangle C) (hU : U ∈ distTriang C) (sigma : U ⟶ T)
    (hsigma₁ : S sigma.hom₁) (hsigma₂ : S sigma.hom₂) (hsigma₃ : S sigma.hom₃)
    (rho : F.mapTriangle.obj U ⟶ Triangle.mk lf b c)
    (hretract₁ : uX.app (MorphismProperty.Over.mk ⊤ sigma.hom₁ hsigma₁) ≫
      rho.hom₁ = 𝟙 LX)
    (hretract₂ : uY.app (MorphismProperty.Over.mk ⊤ sigma.hom₂ hsigma₂) ≫
      rho.hom₂ = 𝟙 LY) :
    ∀ W : D, Function.Bijective (fun phi : K ⟶ W ↦
      ((MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F).op ⋙
        yoneda.obj W).ιColimitType
          (Opposite.op (MorphismProperty.Over.mk ⊤ sigma.hom₃ hsigma₃))
          (rho.hom₃ ≫ phi)) := by
  sorry

end CategoryTheory.Functor
