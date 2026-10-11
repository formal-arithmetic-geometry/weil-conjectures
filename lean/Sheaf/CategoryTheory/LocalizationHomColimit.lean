/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Hom sets in a left localization

Source: Stacks Project, Categories Tag 05Q0 and Derived Categories Tag 0FND
(blueprint: lem-pc-left-localization-hom-colimit).
-/

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- (blueprint: lem-pc-left-localization-hom-colimit) Stacks, Categories Tag 05Q0:
the objects of `S.Under ⊤ X` are denominators `s : X ⟶ I` in `S`, and its arrows are
commuting triangles. The colimit diagram takes `s` to `Hom(Y,I)` and a triangle to
postcomposition. A representative `f : Y ⟶ I` maps to `Q(f) ≫ Q(s)⁻¹`.

For surjectivity, represent each localized morphism by a left fraction (Tag 04VE).
For injectivity, equality of left fractions gives a common later denominator with
equal numerators (Tag 04VF). The two properties make the displayed map bijective.
For the identity multiplicative system, the identity denominator gives the ordinary
Hom bijection. -/
theorem localization_hom_colimit
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization S] (X Y : C) :
    ∃ e : colimit ((MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X) ⋙
        (uliftCoyoneda.{u} (C := C)).obj (Opposite.op Y)) ≃ (Q.obj Y ⟶ Q.obj X),
      ∀ (s : S.Under ⊤ X) (f : Y ⟶ s.right),
        e (colimit.ι ((MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X) ⋙
          (uliftCoyoneda.{u} (C := C)).obj (Opposite.op Y)) s (ULift.up f)) =
          (MorphismProperty.LeftFraction.mk f s.hom s.prop).map Q
            (Localization.inverts Q S) := by
  sorry

end CategoryTheory
