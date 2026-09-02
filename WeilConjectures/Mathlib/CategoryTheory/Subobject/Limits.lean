/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Image subobjects and epimorphisms

We record two facts about the image subobject `imageSubobject f` of a morphism `f`:
precomposing `f` with an epimorphism does not change it, and a morphism into a subobject
`T` of `X` is an epimorphism as soon as the image of the composition with `T.arrow` is `T`.

## Main results

- `CategoryTheory.Limits.imageSubobject_comp_of_epi`
- `CategoryTheory.Limits.epi_of_imageSubobject_comp_arrow_eq`
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open Subobject

variable {C : Type u} [Category.{v} C]

section

variable [Balanced C] [HasImages C] [HasEqualizers C] {A B X : C}

/-- Precomposing with an epimorphism does not change the image subobject. -/
lemma imageSubobject_comp_of_epi (e : A ⟶ B) [Epi e] (m : B ⟶ X) :
    imageSubobject (e ≫ m) = imageSubobject m := by
  have : IsIso (image.preComp e m) := isIso_of_mono_of_epi _
  exact mk_eq_mk_of_comm _ _ (asIso (image.preComp e m)) (image.preComp_ι e m)

/-- If the image of `q ≫ T.arrow` is the whole of the subobject `T`, then `q` is an
epimorphism. -/
lemma epi_of_imageSubobject_comp_arrow_eq {T : Subobject X} (q : A ⟶ (T : C))
    (hq : imageSubobject (q ≫ T.arrow) = T) : Epi q := by
  have hfac : factorThruImageSubobject q ≫ (imageSubobject q).arrow = q :=
    imageSubobject_arrow_comp q
  have h₀ : imageSubobject (q ≫ T.arrow) =
      Subobject.mk ((imageSubobject q).arrow ≫ T.arrow) := by
    conv_lhs => rw [← hfac]
    rw [Category.assoc, imageSubobject_comp_of_epi, imageSubobject_mono]
  have h₁ : Subobject.mk ((imageSubobject q).arrow ≫ T.arrow) = Subobject.mk T.arrow := by
    rw [← h₀, hq, Subobject.mk_arrow]
  have h₂ : (Subobject.isoOfMkEqMk ((imageSubobject q).arrow ≫ T.arrow) T.arrow h₁).hom =
      (imageSubobject q).arrow := by
    rw [← cancel_mono T.arrow]
    simp
  have : IsIso (imageSubobject q).arrow :=
    h₂ ▸ (inferInstance :
      IsIso (Subobject.isoOfMkEqMk ((imageSubobject q).arrow ≫ T.arrow) T.arrow h₁).hom)
  rw [← hfac]
  infer_instance

end

end CategoryTheory.Limits
