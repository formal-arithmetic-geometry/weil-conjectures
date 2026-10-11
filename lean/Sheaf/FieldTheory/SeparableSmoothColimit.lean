/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.FieldTheory.FgSeparableSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Separable extensions as colimits of smooth subalgebras

Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: lem-kun-separable-smooth-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FieldTheory

/-- The inclusion diagram of finitely generated smooth subalgebras of a field extension.
Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: lem-kun-separable-smooth-colimit). -/
def smoothSubalgebraDiagram (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] :
    {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG} ⥤ CommRingCat :=
  { obj := fun A => CommRingCat.of A.1
    map := fun {A B} f =>
      CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
    map_id := by intros; ext; rfl
    map_comp := by intros; ext; rfl }

/-- The cocone from smooth subalgebras to their ambient field, with inclusion maps.
Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: lem-kun-separable-smooth-colimit). -/
def smoothSubalgebraCocone (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] : Cocone (smoothSubalgebraDiagram K L) :=
  { pt := CommRingCat.of L
    ι :=
      { app := fun A => CommRingCat.ofHom A.1.val.toRingHom
        naturality := by intros; ext; rfl } }

/-- For any separable field extension `L/K`, the full collection of finitely generated smooth
`K`-subalgebras of `L` is nonempty and directed under inclusion, and its union is `L`.
Its canonical cocone of inclusions is a colimit, and its image under `Spec` is a limit cone of
affine smooth `K`-schemes with affine transition maps.

Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: lem-kun-separable-smooth-colimit). For each finitely generated subextension of
`L/K`, apply `fg_separable_extension_is_filtered_colimit_smooth`. Every finite subset of `L`
lies in one of the resulting smooth subalgebras; applying this to generators of two such
subalgebras proves directedness. The union is the ring colimit. The `Spec` functor sends its
opposite cone to a limit cone, and maps between affine schemes are affine. -/
theorem separable_extension_is_filtered_colimit_smooth
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hsep : Algebra.IsSeparableExtension K L) :
    Nonempty {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG} ∧
      Directed (· ≤ ·)
        (fun A : {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG} => A.1) ∧
      (∀ x : L, ∃ A : {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG}, x ∈ A.1) ∧
      Nonempty (IsColimit (smoothSubalgebraCocone K L)) ∧
      Nonempty (IsLimit (Scheme.Spec.mapCone (smoothSubalgebraCocone K L).op)) ∧
      (∀ A : {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG},
        Algebra.Smooth K A.1) ∧
      (∀ (A B : {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG}) (f : B ⟶ A),
        IsAffineHom
        (Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (leOfHom f)).toRingHom))) := by
  sorry

end FieldTheory
