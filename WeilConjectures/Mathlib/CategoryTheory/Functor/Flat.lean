/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.Flat

/-!

# The pointwise formula for left Kan extension, without smallness

`CategoryTheory.Functor.lanEvaluationIsoColim` in Mathlib identifies the evaluation of the
left Kan extension functor `F.lan` at `X` with the colimit over the comma category
`CostructuredArrow F X`, but only for small categories. This file provides the same
isomorphism assuming only that the pointwise left Kan extensions along `F` exist and that
the colimits of shape `CostructuredArrow F X` exist in the target
(`CategoryTheory.Functor.lanEvaluationIsoColim'`). It is what makes left Kan extension along
a representably flat functor left exact when the target has exact filtered colimits of
the relevant size, see
`CategoryTheory.GrothendieckTopology.preservesFiniteLimits_op_lan_overPullback`.

This is taken from the `proetale` dependency
(`Proetale.Topology.Comparison.CohomologyComparison`), which is not otherwise imported here.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Variant of `CategoryTheory.Functor.lanEvaluationIsoColim` without the smallness
assumptions on the categories involved: the evaluation of `F.lan` at `X` is the colimit
over the costructured arrows over `X`. -/
noncomputable def lanEvaluationIsoColim' (F : C ⥤ D) (X : D)
    [∀ G : C ⥤ H, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F X) H] :
    F.lan ⋙ (evaluation D H).obj X ≅
      (Functor.whiskeringLeft _ _ H).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G ↦
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ ↦ by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ H) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

end CategoryTheory.Functor
