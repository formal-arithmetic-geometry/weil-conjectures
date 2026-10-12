/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# A product with a single nonzero factor

If all factors of a product but one are zero objects, then a morphism into the product is an
isomorphism as soon as its component in the remaining factor is.
-/

@[expose] public section

namespace CategoryTheory.Limits

/-- A morphism `Pi.lift g` into a product `∏ᶜ f` is an isomorphism if its component `g t` is an
isomorphism and all other factors `f b`, `b ≠ t`, are zero objects. -/
lemma isIso_pi_lift_of_isZero {β : Type*} {C : Type*} [Category* C] {f : β → C}
    [HasProduct f] {A : C} (g : ∀ b, A ⟶ f b) (t : β) (ht : IsIso (g t))
    (hz : ∀ b, b ≠ t → IsZero (f b)) : IsIso (Pi.lift g) := by
  classical
  refine ⟨⟨Pi.π f t ≫ inv (g t), by simp, Pi.hom_ext _ _ fun b ↦ ?_⟩⟩
  by_cases h : b = t
  · subst h
    simp
  · exact (hz b h).eq_of_tgt _ _

end CategoryTheory.Limits
