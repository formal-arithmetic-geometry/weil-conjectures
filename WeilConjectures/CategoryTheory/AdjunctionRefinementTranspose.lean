/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Basic
/-! Transport of adjunction transposes along a normalized comparison square.
(blueprint: new-lem-pur-ringed-refinement-adjunction-transpose). -/
@[expose] public section
set_option autoImplicit false
universe k
namespace CategoryTheory
private theorem evaluation_transpose
    {A C D E : Type k}
    [Category.{k} A] [Category.{k} C] [Category.{k} D] [Category.{k} E]
    {F : A ⥤ C} {G : C ⥤ A} {F' : D ⥤ E} {G' : E ⥤ D}
    (a : F ⊣ G) (b : F' ⊣ G') (V : A ⥤ D) (W : C ⥤ E)
    (l : F ⋙ W ≅ V ⋙ F') (r : G ⋙ V ≅ W ⋙ G')
    (hu : ∀ M : A, V.map (a.unit.app M) ≫ r.hom.app (F.obj M) ≫
      G'.map (l.hom.app M) = b.unit.app (V.obj M))
    {M : A} {N : C} (f : F.obj M ⟶ N) :
    V.map (a.homEquiv _ _ f) ≫ r.hom.app N =
      b.homEquiv _ _ (l.inv.app M ≫ W.map f) := by
  rw [a.homEquiv_unit, b.homEquiv_unit]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := r.hom.naturality f
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  rw [hn]
  have hu : V.map (a.unit.app M) ≫ r.hom.app (F.obj M) =
      b.unit.app (V.obj M) ≫ G'.map (l.inv.app M) := by
    rw [← hu M]
    have hi := (G'.mapIso (l.app M)).hom_inv_id
    change G'.map (l.hom.app M) ≫ G'.map (l.inv.app M) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  rw [← Category.assoc, hu, Category.assoc]

/-- Adjunction transposes preserve a compared morphism and changes of its endpoints.
Source: coefficient supplement Step 10; Mathlib Adjunction.Basic.
Proof: expand Hom transposes using the units. Naturality of the right comparison
and its unit equation give the evaluation-transpose identity. Apply naturality
in the target to absorb t, use the displayed comparison equation, cancel the
left comparison with its inverse, and apply naturality in the source to absorb s.
(blueprint: new-lem-pur-ringed-refinement-adjunction-transpose). -/
theorem adjunctionRefinementTranspose
    {A C D E : Type k}
    [Category.{k} A] [Category.{k} C] [Category.{k} D] [Category.{k} E]
    {F : A ⥤ C} {G : C ⥤ A} {F' : D ⥤ E} {G' : E ⥤ D}
    (a : F ⊣ G) (b : F' ⊣ G') (V : A ⥤ D) (W : C ⥤ E)
    (l : F ⋙ W ≅ V ⋙ F') (r : G ⋙ V ≅ W ⋙ G')
    (hu : ∀ M : A, V.map (a.unit.app M) ≫ r.hom.app (F.obj M) ≫
      G'.map (l.hom.app M) = b.unit.app (V.obj M))
    {M : A} {N : C} {M' : D} {N' : E}
    (f : F.obj M ⟶ N) (s : V.obj M ⟶ M') (t : W.obj N ⟶ N')
    (h : F'.obj M' ⟶ N')
    (hf : W.map f ≫ t = l.hom.app M ≫ F'.map s ≫ h) :
    V.map (a.homEquiv _ _ f) ≫ r.hom.app N ≫ G'.map t =
      s ≫ b.homEquiv _ _ h := by
  calc
    _ = (V.map (a.homEquiv M N f) ≫ r.hom.app N) ≫ G'.map t :=
      (Category.assoc _ _ _).symm
    _ = b.homEquiv (V.obj M) (W.obj N)
          (l.inv.app M ≫ W.map f) ≫ G'.map t :=
      congrArg (fun z ↦ z ≫ G'.map t) (evaluation_transpose a b V W l r hu f)
    _ = b.homEquiv (V.obj M) N' ((l.inv.app M ≫ W.map f) ≫ t) :=
      (b.homEquiv_naturality_right (l.inv.app M ≫ W.map f) t).symm
    _ = b.homEquiv (V.obj M) N' (F'.map s ≫ h) := by
      apply congrArg (b.homEquiv (V.obj M) N')
      calc
        _ = l.inv.app M ≫ (W.map f ≫ t) := Category.assoc _ _ _
        _ = l.inv.app M ≫ (l.hom.app M ≫ F'.map s ≫ h) :=
          congrArg (fun z ↦ l.inv.app M ≫ z) hf
        _ = F'.map s ≫ h := by
          rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    _ = s ≫ b.homEquiv M' N' h := b.homEquiv_naturality_left s h

end CategoryTheory
