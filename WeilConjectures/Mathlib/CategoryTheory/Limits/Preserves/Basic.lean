/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Natural transformations between colimit-preserving functors

If `α : Φ ⟶ Ψ` is a natural transformation between two functors which both preserve the
colimit of a diagram `K`, and if `α` is an isomorphism on all the objects `K.obj j`, then
`α` is also an isomorphism on the colimit of `K`.

## Main results

- `CategoryTheory.Limits.isIso_app_of_isColimit`

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {Φ Ψ : C ⥤ D} (α : Φ ⟶ Ψ)
  {J : Type*} [Category* J] {K : J ⥤ C} {c : Cocone K}

/-- If a natural transformation between two functors which preserve the colimit of a diagram
`K` is an isomorphism on the objects of `K`, then it is an isomorphism on the colimit. -/
lemma isIso_app_of_isColimit (hc : IsColimit c) [PreservesColimit K Φ] [PreservesColimit K Ψ]
    (h : ∀ j, IsIso (α.app (K.obj j))) : IsIso (α.app c.pt) := by
  have hi : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := h
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  have heq : α.app c.pt = ((isColimitOfPreserves Φ hc).coconePointsIsoOfNatIso
      (isColimitOfPreserves Ψ hc) (asIso (Functor.whiskerLeft K α))).hom := by
    refine (isColimitOfPreserves Φ hc).hom_ext fun j ↦ ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact α.naturality (c.ι.app j)
  rw [heq]
  infer_instance

end CategoryTheory.Limits
