/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles

/-!
# Exactness of everywhere-defined left derived functors

Source: Stacks Project, Derived Categories, Definition 05S9 and Proposition 05SE.
-/

@[expose] public section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- In Situation 05S8, when the left derived values exist at every object, the
universal left derived functor is exact (Stacks Project, Tags 05S9 and 05SE).

The hypothesis `hLF` records that `LF` is characterized by the universal
(right Kan extension) property along the localization functor `Q`. -/
theorem leftDerived_exact_when_defined
    (D : Type u) [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (D' : Type u') [Category.{v'} D'] [HasZeroObject D'] [HasShift D' ℤ]
    [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (L : Type u'') [Category.{v''} L] [HasZeroObject L] [HasShift L ℤ]
    [Preadditive L] [∀ n : ℤ, (shiftFunctor L n).Additive]
    [Pretriangulated L] [CategoryTheory.IsTriangulated L]
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty D)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (Q : D ⥤ L) [Q.CommShift ℤ] [Q.IsTriangulated]
    [Q.IsLocalization S]
    (_hQ : Q.IsStrictLocalizationAt S)
    (LF : L ⥤ D')
    (α : Q ⋙ LF ⟶ F)
    (hLF : LF.IsRightKanExtension α)
    (hdefined : ∀ X : D, F.IsTriangulatedLeftDerivedDefinedAt S hS X) :
    ∃ (_ : LF.CommShift ℤ), LF.IsTriangulated := by
  classical
  let : S.HasLeftCalculusOfFractions := hS.1.1.1
  obtain ⟨hshift, hα⟩ := rightKanExtension_coherentShift F Q LF α hLF
  let : LF.CommShift ℤ := hshift
  let : NatTrans.CommShift α ℤ := hα
  have hsource : (Q ⋙ LF).IsTriangulated := by
    constructor
    intro T hT
    exact leftDerived_kan_map_source_distinguished D D' L F S hS Q LF α hLF
      hdefined hα T hT
  let : (Q ⋙ LF).IsTriangulated := hsource
  have := Localization.essSurj_mapArrow Q S
  refine ⟨hshift, ⟨fun T hT ↦ ?_⟩⟩
  obtain ⟨T₀, e, hT₀⟩ := (Q.distTriang_iff T).1 hT
  exact Pretriangulated.isomorphic_distinguished _
    ((Q ⋙ LF).map_distinguished T₀ hT₀) _
    (LF.mapTriangle.mapIso e ≪≫ (mapTriangleCompIso Q LF).symm.app T₀)

end CategoryTheory.Functor
