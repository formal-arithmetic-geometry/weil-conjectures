/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Yoneda
import Sheaf.CategoryTheory.DerivedFunctorTriangleRetractionHomColimit

/-! # Hom-colimit comparison for a fixed derived cone

Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause (dual argument).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- A fixed cone of the induced first map represents the third denominator Hom-colimit.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause, specifically the
TR3 comparison and five-lemma argument; Categories, Tags 05PZ and 0A1T.
(blueprint: lem-pur-derived-fixed-cone-hom-colimit).

Proof: Complete the supplied denominator square to a distinguished source triangle
by TR1 and MS6. Apply the exact functor F. The supplied equation between the two
retractions extends by TR3 to a map gamma from its third vertex to K. This gives
sZ, g' and r = gamma, including the second-square equation F(g') r = beta b.
Index incoming distinguished denominator triangles over this source triangle by the
cofiltered category of Tag 05R9. Its vertex projections are initial. Apply Hom(-,W)
to their F-images and take filtered colimits of the five-term exact sequences of
abelian groups. Compare with the exact sequence for the fixed triangle (LX,LY,K).
The first two comparison maps are inverse to the supplied cone Hom-colimit maps:
the retraction identities show this at the chosen stages. At the shifted terms the
same argument uses W[-1] and the shift equivalence. Exactness of filtered colimits
and the five lemma give a bijection in the middle, induced by gamma followed by
each morphism K -> W. Initiality of the third projection transports this bijection
to the full denominator category at T.obj3; the denominator change-of-base
comparison (05SB) identifies refinement over the chosen source triangle with the
original diagram. These comparisons preserve the representative gamma followed
by that morphism, giving exactly the displayed function. No supplied third value
or second derived map, no cone on K, and no value-triangle completion theorem is used.

Edge cases: K is any distinguished completion of lf, not a chosen arbitrary witness
of an existence axiom. The zero first map gives the usual split cone. When S consists
of isomorphisms, the comparison is the ordinary TR3 isomorphism on third vertices. -/
theorem leftDerived_fixedCone_homColimit
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
    (sX : S.Over ⊤ T.obj₁) (sY : S.Over ⊤ T.obj₂)
    (f' : sX.left ⟶ sY.left)
    (hsq : sX.hom ≫ T.mor₁ = f' ≫ sY.hom)
    (alpha : F.obj sX.left ⟶ LX) (beta : F.obj sY.left ⟶ LY)
    (halpha : uX.app sX ≫ alpha = 𝟙 LX)
    (hbeta : uY.app sY ≫ beta = 𝟙 LY)
    (hret : F.map f' ≫ beta = alpha ≫ lf) :
    ∃ (sZ : S.Over ⊤ T.obj₃) (g' : sY.left ⟶ sZ.left)
      (r : F.obj sZ.left ⟶ K),
      sY.hom ≫ T.mor₂ = g' ≫ sZ.hom ∧
      F.map g' ≫ r = beta ≫ b ∧
      ∀ W : D, Function.Bijective (fun phi : K ⟶ W ↦
        ((MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F).op ⋙
          yoneda.obj W).ιColimitType (Opposite.op sZ) (r ≫ phi)) := by
  let : S.IsCompatibleWithTriangulation := hS.2
  obtain ⟨Z', g', h', hU⟩ := distinguished_cocone_triangle f'
  let U := Triangle.mk f' g' h'
  obtain ⟨sZ, hsZ, hgsq, hhsq⟩ :=
    MorphismProperty.compatible_with_triangulation (W := S) U T hU hT
      sX.hom sY.hom sX.prop sY.prop hsq.symm
  let sigma : U ⟶ T := Triangle.homMk _ _ sX.hom sY.hom sZ
    hsq.symm hgsq hhsq
  obtain ⟨r, hgr, hhr⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj U) (Triangle.mk lf b c) (F.map_distinguished U hU) hK
    alpha beta hret
  let rho : F.mapTriangle.obj U ⟶ Triangle.mk lf b c :=
    Triangle.homMk _ _ alpha beta r hret hgr hhr
  refine ⟨MorphismProperty.Over.mk ⊤ sZ hsZ, g', r, hgsq.symm, hgr, ?_⟩
  exact leftDerived_triangle_retraction_homColimit F S hS T hT LX LY hX hY
    uX uY huX huY lf K b c hK U hU sigma sX.prop sY.prop hsZ rho halpha hbeta

end CategoryTheory.Functor
