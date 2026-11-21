/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedFunctorTriangles
import WeilConjectures.CategoryTheory.LeftDerivedKanTriangleValueComparison

/-! # Distinguished source triangles under a left derived Kan extension

Source: Stacks Project, Derived Categories, Lemmas Tags 05SA, 05SU, 05SC.
-/

@[expose] public section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- The supplied shift-compatible Kan extension preserves distinguished source triangles.
Source: Stacks Project, Derived Categories, Lemmas Tags 05SA, 05SU, 05SC,
and the pointwise Kan interpretation of Definition Tag 05S9. -/
theorem leftDerived_kan_map_source_distinguished
    (D : Type u) [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (D' : Type u') [Category.{v'} D'] [HasZeroObject D'] [HasShift D' ℤ]
    [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (L : Type u'') [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty D)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (Q : D ⥤ L) [Q.CommShift ℤ]
    [Q.IsLocalization S]
    (LF : L ⥤ D') [LF.CommShift ℤ]
    (α : Q ⋙ LF ⟶ F)
    (hLF : LF.IsRightKanExtension α)
    (hdefined : ∀ X : D, F.IsTriangulatedLeftDerivedDefinedAt S hS X)
    (hα : NatTrans.CommShift α ℤ) (T : Triangle D) (hT : T ∈ distTriang D) :
    (Q ⋙ LF).mapTriangle.obj T ∈ distTriang D' := by
  classical
  let : S.HasRightCalculusOfFractions := hS.1.1.2
  let : LF.IsRightKanExtension α := hLF
  have hAt (X : D) : Q.HasPointwiseRightKanExtensionAt F (Q.obj X) := by
    obtain ⟨Y, hY⟩ := hdefined X
    obtain ⟨hc, u, s₀, r, hr, hfac⟩ := hY
    exact (leftDerived_defined_pointwiseKan_bridge S Q F X Y
      ⟨hc, u, s₀, r, hr, hfac⟩ u ⟨s₀, r, hr, hfac⟩).1
  let : Q.HasPointwiseRightKanExtension F := fun Y ↦ by
    have := Localization.essSurj Q S
    rw [← hasPointwiseRightKanExtensionAt_iff_of_iso Q F (Q.objObjPreimageIso Y)]
    exact hAt _
  obtain ⟨LX, LY, LZ, hX, hY, hZ, uX, uY, uZ, huX, huY, huZ,
      lf, lg, lh, hf, hg, hh, htri⟩ :=
    leftDerived_map_distinguished_of_two_defined F S hS T hT
      (Or.inl ⟨hdefined T.obj₁, hdefined T.obj₂⟩)
  obtain ⟨e⟩ := leftDerived_kan_triangle_value_comparison D D' L F S hS Q LF α hLF hα T
    LX LY LZ hX hY hZ uX huX uY huY uZ huZ lf lg lh hf hg hh
  exact isomorphic_distinguished _ htri _ e

end CategoryTheory.Functor
