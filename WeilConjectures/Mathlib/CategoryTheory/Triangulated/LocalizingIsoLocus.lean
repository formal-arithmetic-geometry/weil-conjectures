/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Invertibility propagates to the localizing closure

The isomorphism locus of a shift-compatible natural transformation between exact,
coproduct-preserving functors is a triangulated subcategory closed under coproducts and
retracts; hence if it contains a class `S`, it contains the localizing closure of `S`.

## Implementation details

The localizing closure is written as its defining intersection in the statement.
Coproduct closure uses arbitrary colimit cocones, including singleton coproducts,
so it includes closure under isomorphisms. The source category can itself be a
localizing subcategory.
-/

@[expose] public section

set_option autoImplicit false

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.NatTrans

/-- The isomorphism locus of a shift-compatible natural transformation between exact,
coproduct-preserving functors is triangulated and closed under coproducts and retracts.
If it contains `S`, it contains the intersection of all triangulated subcategories
containing `S` and closed under arbitrary coproducts, namely the localizing closure. -/
theorem isoLocus_localizing
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (S : ObjectProperty C) (F₁ F₂ : C ⥤ D)
    [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₁.IsTriangulated] [F₂.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F₁]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F₂]
    (η : F₁ ⟶ F₂) [NatTrans.CommShift η ℤ] :
    η.isoLocus.IsTriangulated ∧
      (∀ I : Type w, Nonempty (η.isoLocus.IsClosedUnderColimitsOfShape (Discrete I))) ∧
      Nonempty η.isoLocus.IsStableUnderRetracts ∧
      (S ≤ η.isoLocus →
        sInf {P : ObjectProperty C | S ≤ P ∧ P.IsTriangulated ∧
          ∀ I : Type w, Nonempty (P.IsClosedUnderColimitsOfShape (Discrete I))} ≤
            η.isoLocus) := by
  have hcolim : ∀ I : Type w,
      Nonempty (η.isoLocus.IsClosedUnderColimitsOfShape (Discrete I)) := by
    intro I
    refine ⟨⟨?_⟩⟩
    intro X ⟨p⟩
    have hη : ∀ j, IsIso ((Functor.whiskerLeft p.diag η).app j) := p.prop_diag_obj
    have : IsIso (Functor.whiskerLeft p.diag η) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit p.diag η _ p.isColimit
  refine ⟨inferInstance, hcolim, ⟨inferInstance⟩, ?_⟩
  intro hS
  exact sInf_le ⟨hS, inferInstance, hcolim⟩

end CategoryTheory.NatTrans
