/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
public import Mathlib.Topology.Sheaves.Stalks

/-! # Stalks of nested slice extensions

Nested slice extensions of a sheaf admit a map inducing isomorphisms on stalks at points of the
smaller open.

## References

* [Stacks Project, Tags 0A38 and 00A5](https://stacks.math.columbia.edu/tag/0A38)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- Nested slice extensions of a sheaf admit a map inducing isomorphisms at interior points. -/
theorem nested_slice_extension_stalks {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) (hVU : V ≤ U) :
    ∃ g : (siteExtensionByZeroPresheaf V).obj (F.over V).obj ⟶
        (siteExtensionByZeroPresheaf U).obj (F.over U).obj,
      ∀ x : X, x ∈ V →
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g) := by
  classical
  let (W W' : Opens X) : DecidableEq (W ⟶ W') := Classical.decEq _
  let g : (siteExtensionByZeroPresheaf V).obj (F.over V).obj ⟶
      (siteExtensionByZeroPresheaf U).obj (F.over U).obj := {
    app := fun W ↦ AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun φ : W.unop ⟶ V ↦
      DirectSum.of (fun ψ : W.unop ⟶ U ↦ F.obj.obj W) (φ ≫ homOfLE hVU))
    naturality := by
      intro W W' a
      apply AddCommGrpCat.hom_ext
      dsimp [siteExtensionByZeroPresheaf, siteExtensionByZeroPresheafObj,
        siteExtensionByZeroRestrict, siteExtensionByZeroSection]
      apply DirectSum.addHom_ext
      intro i s
      simp only [AddMonoidHom.comp_apply]
      dsimp [Sheaf.over, GrothendieckTopology.overPullback,
        Functor.sheafPushforwardContinuous] at s ⊢
      simp only [Over.homMk_left, Quiver.Hom.op_unop]
      simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
      congr 1 }
  have hbij (W : Opens X) (hWV : W ≤ V) : Function.Bijective (g.app (op W)) := by
    let r : (DirectSum (W ⟶ U) (fun _ ↦ F.obj.obj (op W))) →+
        DirectSum (W ⟶ V) (fun _ ↦ F.obj.obj (op W)) :=
      DirectSum.toAddMonoid fun _ ↦
        DirectSum.of (fun _ : W ⟶ V ↦ F.obj.obj (op W)) (homOfLE hWV)
    have hl : r.comp (g.app (op W)).hom = AddMonoidHom.id _ := by
      apply DirectSum.addHom_ext
      intro i s
      change r ((DirectSum.toAddMonoid (fun φ : W ⟶ V ↦
          DirectSum.of (fun _ : W ⟶ U ↦ F.obj.obj (op W)) (φ ≫ homOfLE hVU)))
          (DirectSum.of _ i s)) = DirectSum.of _ i s
      simp only [r, DirectSum.toAddMonoid_of]
      congr 1
    have hr : (g.app (op W)).hom.comp r = AddMonoidHom.id _ := by
      apply DirectSum.addHom_ext
      intro i s
      change (DirectSum.toAddMonoid (fun φ : W ⟶ V ↦
          DirectSum.of (fun _ : W ⟶ U ↦ F.obj.obj (op W)) (φ ≫ homOfLE hVU)))
          (r (DirectSum.of _ i s)) = DirectSum.of _ i s
      simp only [r, DirectSum.toAddMonoid_of]
      congr 1
    have hl' : Function.LeftInverse r (g.app (op W)).hom :=
      fun s ↦ DFunLike.congr_fun hl s
    have hr' : Function.RightInverse r (g.app (op W)).hom :=
      fun s ↦ DFunLike.congr_fun hr s
    change Function.Bijective (g.app (op W)).hom
    exact ⟨hl'.injective, hr'.surjective⟩
  refine ⟨g, ?_⟩
  intro x hx
  let P : X.Presheaf AddCommGrpCat.{u} := (siteExtensionByZeroPresheaf V).obj (F.over V).obj
  let Q : X.Presheaf AddCommGrpCat.{u} := (siteExtensionByZeroPresheaf U).obj (F.over U).obj
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro s t hst
    obtain ⟨W₁, hW₁, hxW₁, s, rfl⟩ := P.exists_le_germ_eq s hx
    obtain ⟨W₂, hW₂, hxW₂, t, rfl⟩ := P.exists_le_germ_eq t hx
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
    obtain ⟨W, hxW, i₁, i₂, heq⟩ := Q.germ_eq x hxW₁ hxW₂ _ _ hst
    have heq' : g.app (op W) (P.map i₁.op s) =
        g.app (op W) (P.map i₂.op t) := by
      simpa only [P, Q, g.naturality_apply] using heq
    exact P.germ_ext W hxW i₁ i₂ ((hbij W (i₁.le.trans hW₁)).1 heq')
  · intro t
    obtain ⟨W, hWV, hxW, t, ht⟩ := Q.exists_le_germ_eq t hx
    obtain ⟨s, hs⟩ := (hbij W hWV).2 t
    refine ⟨P.germ W x hxW s, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hs]
    exact ht

end TopCat.Sheaf
