/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The rationalization diagram of an object of a preadditive category

For an object `X` of a preadditive category, `CategoryTheory.Preadditive.rationalizationDiagram X`
is the sequence `X --1--> X --2--> X --3--> ⋯`, the map from stage `k` to stage `n` being
multiplication by `(k + 1) (k + 2) ⋯ n`. For abelian groups its colimit is `X ⊗ ℚ`; it is zero
exactly when `X` is torsion. Additive functors preserve the diagram
(`CategoryTheory.Functor.mapRationalizationDiagramIso`).
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The sequence `X --1--> X --2--> X --3--> ⋯`: the map from stage `k` to stage `n` is
multiplication by `(k + 1).ascFactorial (n - k) = (k + 1) ⋯ n`. -/
@[simps obj]
def rationalizationDiagram (X : C) : ℕ ⥤ C where
  obj _ := X
  map {k n} _ := (k + 1).ascFactorial (n - k) • 𝟙 X
  map_id k := by simp
  map_comp {k n p} f g := by
    have hkn := leOfHom f
    have hnp := leOfHom g
    rw [Preadditive.smul_comp, Preadditive.comp_smul, Category.comp_id, smul_smul,
      ← Nat.ascFactorial_mul_ascFactorial, Nat.mul_comm]
    congr 3
    omega

lemma rationalizationDiagram_map (X : C) {k n : ℕ} (f : k ⟶ n) :
    (rationalizationDiagram X).map f = (k + 1).ascFactorial (n - k) • 𝟙 X :=
  rfl

/-- The coprojections of the colimit of the rationalization diagram: the coprojection at
stage `k` is `(k + 1) ⋯ (k + N)` times the coprojection at stage `k + N`. -/
lemma colimit_ι_rationalizationDiagram (X : C) [HasColimit (rationalizationDiagram X)]
    (k N : ℕ) :
    colimit.ι (rationalizationDiagram X) k =
      (k + 1).ascFactorial N • colimit.ι (rationalizationDiagram X) (k + N) := by
  rw [← colimit.w (rationalizationDiagram X) (homOfLE (Nat.le_add_right k N)),
    rationalizationDiagram_map, Preadditive.smul_comp, Category.id_comp, Nat.add_sub_cancel_left]

/-- The colimit of the rationalization diagram is zero if and only if all its coprojections
vanish. -/
lemma isZero_colimit_rationalizationDiagram_iff (X : C) [HasColimit (rationalizationDiagram X)] :
    IsZero (colimit (rationalizationDiagram X)) ↔
      ∀ k, colimit.ι (rationalizationDiagram X) k = 0 := by
  refine ⟨fun h k ↦ h.eq_of_tgt _ _, fun h ↦ ?_⟩
  rw [IsZero.iff_id_eq_zero]
  exact colimit.hom_ext fun k ↦ by simp [h k]

end CategoryTheory.Preadditive

namespace CategoryTheory.Functor

open Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- An additive functor maps the rationalization diagram of `X` to that of its image. -/
@[simps!]
def mapRationalizationDiagramIso (G : C ⥤ D) [G.Additive] (X : C) :
    rationalizationDiagram X ⋙ G ≅ rationalizationDiagram (G.obj X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    simp [rationalizationDiagram_map, Functor.map_nsmul]

end CategoryTheory.Functor

namespace CategoryTheory.Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Isomorphic objects have isomorphic rationalization diagrams. -/
@[simps!]
def rationalizationDiagramIsoOfIso {X Y : C} (e : X ≅ Y) :
    rationalizationDiagram X ≅ rationalizationDiagram Y :=
  NatIso.ofComponents (fun _ ↦ e) fun f ↦ by simp [rationalizationDiagram_map]

end CategoryTheory.Preadditive
