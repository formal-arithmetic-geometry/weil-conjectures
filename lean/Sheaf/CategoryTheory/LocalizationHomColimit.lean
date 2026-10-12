/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Hom sets in a left localization

Source: Stacks Project, Categories Tag 05Q0 and Derived Categories Tag 0FND
(blueprint: lem-pc-left-localization-hom-colimit).
-/

@[expose] public section

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
  classical
  let F := (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X) ⋙
    (uliftCoyoneda.{u} (C := C)).obj (Opposite.op Y)
  let c : F.CoconeTypes :=
    { pt := Q.obj Y ⟶ Q.obj X
      ι s f := (MorphismProperty.LeftFraction.mk f.down s.hom s.prop).map Q
        (Localization.inverts Q S)
      ι_naturality := by
        intro s t a
        funext f
        have := Localization.inverts Q S _ s.prop
        have := Localization.inverts Q S _ t.prop
        apply (cancel_mono (Q.map t.hom)).1
        change (MorphismProperty.LeftFraction.mk (f.down ≫ a.right) t.hom t.prop).map
            Q (Localization.inverts Q S) ≫ Q.map t.hom =
          (MorphismProperty.LeftFraction.mk f.down s.hom s.prop).map
            Q (Localization.inverts Q S) ≫ Q.map t.hom
        simp only [MorphismProperty.LeftFraction.map, Functor.map_comp,
          Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [← MorphismProperty.Under.w a, Q.map_comp]
        simp only [IsIso.inv_hom_id_assoc] }
  have hc : c.IsColimit := by
    constructor
    constructor
    · intro x y h
      obtain ⟨s, f, rfl⟩ := F.ιColimitType_jointly_surjective x
      obtain ⟨t, g, rfl⟩ := F.ιColimitType_jointly_surjective y
      change (MorphismProperty.LeftFraction.mk f.down s.hom s.prop).map Q
          (Localization.inverts Q S) =
        (MorphismProperty.LeftFraction.mk g.down t.hom t.prop).map Q
          (Localization.inverts Q S) at h
      obtain ⟨J, a, b, hs, hf, ha⟩ :=
        (MorphismProperty.LeftFraction.map_eq_iff Q S _ _).mp h
      let r : S.Under ⊤ X := MorphismProperty.Under.mk ⊤ (s.hom ≫ a) ha
      let α : s ⟶ r := MorphismProperty.Under.homMk a rfl
      let β : t ⟶ r := MorphismProperty.Under.homMk b hs.symm
      apply F.ιColimitType_eq_of_map_eq_map f g α β
      change ULift.up (f.down ≫ a) = ULift.up (g.down ≫ b)
      exact congrArg ULift.up hf
    · intro g
      obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction Q S g
      exact ⟨F.ιColimitType (MorphismProperty.Under.mk ⊤ φ.s φ.hs)
        (ULift.up φ.f), hφ.symm⟩
  refine ⟨(Types.colimitEquivColimitType F).trans hc.equiv, ?_⟩
  intro s f
  change hc.equiv ((Types.colimitEquivColimitType F)
    (colimit.ι F s (ULift.up f))) = _
  rw [Types.colimitEquivColimitType_apply]
  rfl

end CategoryTheory
