/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseLeftDerived

/-!
# Left derived functors obtained from left derivability structures

If `Φ : LocalizerMorphism W₁ W₂` is a left derivability structure and
`F : C₂ ⥤ H` is a functor such that `Φ.Derives F` holds, i.e. `Φ.functor ⋙ F`
inverts `W₁`, then `F` has a pointwise left derived functor with respect to
`W₂`, and the counit of any left derived functor of `F` is an isomorphism
on the objects in the image of `Φ.functor`.

These are the duals of the results in
`Mathlib/CategoryTheory/Localization/DerivabilityStructure/Derives.lean`;
the two should be kept in sync.

In mathlib, this file would be part of
`Mathlib/CategoryTheory/Localization/DerivabilityStructure/Derives.lean`.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H] [Category.{v₄} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable {Φ : LocalizerMorphism W₁ W₂} {F : C₂ ⥤ H}

namespace Derives

variable (h : Φ.Derives F) [Φ.IsLeftDerivabilityStructure]

include h

lemma hasPointwiseLeftDerivedFunctor : F.HasPointwiseLeftDerivedFunctor W₂ := by
  rw [hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure Φ F]
  exact Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ h

section

variable {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {LF : D₂ ⥤ H} (α : L₂ ⋙ LF ⟶ F)

lemma isIso_of_isLeftDerivedFunctor (X₁ : C₁) [LF.IsLeftDerivedFunctor α W₂] :
    IsIso (α.app (Φ.functor.obj X₁)) := by
  let G : W₁.Localization ⥤ H := Localization.lift (Φ.functor ⋙ F) h W₁.Q
  let eG := Localization.Lifting.iso W₁.Q W₁ (Φ.functor ⋙ F) G
  have := Functor.isLeftDerivedFunctor_of_inverts W₁ G eG
  have := Functor.hasPointwiseLeftDerivedFunctor_of_inverts (Φ.functor ⋙ F) h
  rw [← Φ.isIso_iff_of_isLeftDerivabilityStructure W₁.Q L₂ F G eG.hom LF α]
  infer_instance

end

end Derives

end LocalizerMorphism

end CategoryTheory
