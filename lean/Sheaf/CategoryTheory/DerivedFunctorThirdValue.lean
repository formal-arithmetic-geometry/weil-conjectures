/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit
import Sheaf.CategoryTheory.LeftDerivedValueMorphism
import Sheaf.CategoryTheory.TriangleMorphismCategory
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- The third vertex has a left-derived value when the first two do.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause
(blueprint: lem-pur-derived-functor-triangles-05sc-third-value).

Proof (dual of the source's construction): choose values A and B with their
essential-constancy cones, and form LF(f) by 05SA. Choose retraction stages for
the two cones. MS2 lifts f to a denominator square; the common-stage factorization
and cofiltered equalization refine the first stage until the retractions alpha
and beta satisfy alpha followed by LF(f) = F(f') followed by beta. Complete f'
to a distinguished triangle and use MS6 to supply its third denominator. Complete
LF(f) to a distinguished triangle (A,B,C). Exactness of F and TR3 extend alpha and
beta to gamma : F(Z') -> C. Use the cofiltered category of denominator triangles
of 05R9; its initial vertex projections transport the A and B cones by 0A1S.
For each W, apply Hom(-,W) to these F-image triangles and take the filtered
colimit over the opposite indexing category. Exactness of filtered colimits
and the five lemma make Hom(C,W) -> colim Hom(F(Z''),W), induced at the chosen
stage by gamma, bijective. The four outer comparisons are inverse to the cone
Hom-colimit bijections; for the shifted terms use W[-1]. The pro criterion 05PY
at gamma supplies an essentially constant cone with value C. Initiality of the
third projection transports it to S/Z. Thus C is a left-derived value at Z.
This construction does not use the parent theorem or any rotation case. -/
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
  sorry

end CategoryTheory.Functor
