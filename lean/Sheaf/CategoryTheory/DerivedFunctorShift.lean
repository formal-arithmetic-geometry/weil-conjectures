/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Left derived values commute with shifts

Source: Stacks Project, Derived Categories, Lemma 05SU(2)
(blueprint: lem-pur-derived-functor-shift-05su).
-/

universe u v uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- In Situation 05S8, left-derived definedness is invariant under shifts, and shifted
values are canonically isomorphic, compatibly with any supplied value cones.
The cone legs specify the values as pro-objects, rather than only their underlying
objects. Their limit property follows from the retraction and common-stage
factorization in `IsEssentiallyConstantProDiagram`. The leg equation uniquely
characterizes the shift comparison; MS5 guarantees the shifted denominator belongs
to `S`, so its proof argument does not restrict the denominators being tested.
Source: Stacks Project, Derived Categories, Lemma 05SU(2)
(blueprint: lem-pur-derived-functor-shift-05su).
The proof shifts the denominator category by the equivalence induced by `[n]`, using
MS5 and its inverse. Exactness transports the essentially constant pro-diagram and
its value through the shift isomorphisms, preserving the cone, retraction, and
factorization conditions. The hom-colimit uniqueness statement
`lem-pc-essentially-constant-pro-hom-colimit` identifies the transported value and
produces the canonical isomorphism; applying the construction with `-n` gives the
reverse implication. -/
theorem isTriangulatedLeftDerivedDefinedAt_shift_iff
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
    (X : C) (n : ℤ) :
    (F.IsTriangulatedLeftDerivedDefinedAt S hS X ↔
      F.IsTriangulatedLeftDerivedDefinedAt S hS ((shiftFunctor C n).obj X)) ∧
      (F.IsTriangulatedLeftDerivedDefinedAt S hS X →
        ∀ (Y Y' : D), F.IsTriangulatedLeftDerivedValue S hS X Y →
          F.IsTriangulatedLeftDerivedValue S hS ((shiftFunctor C n).obj X) Y' →
            let G := MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F
            let Gn := MorphismProperty.Over.forget S ⊤ ((shiftFunctor C n).obj X) ⋙
              Over.forget ((shiftFunctor C n).obj X) ⋙ F
            ∀ (u : (Functor.const (S.Over ⊤ X)).obj Y ⟶ G)
              (u' : (Functor.const (S.Over ⊤ ((shiftFunctor C n).obj X))).obj Y' ⟶ Gn),
              Nonempty (IsLimit (Cone.mk Y u)) → Nonempty (IsLimit (Cone.mk Y' u')) →
                ∃! e : (shiftFunctor D n).obj Y ≅ Y',
                  ∀ (s : S.Over ⊤ X) (hs : S ((shiftFunctor C n).map s.hom)),
                    e.hom ≫ u'.app (MorphismProperty.Over.mk ⊤
                        ((shiftFunctor C n).map s.hom) hs) =
                      (shiftFunctor D n).map (u.app s) ≫
                        (F.commShiftIso n).inv.app s.left) := by
  sorry

end CategoryTheory.Functor
