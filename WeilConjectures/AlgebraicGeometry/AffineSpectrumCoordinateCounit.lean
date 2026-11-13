/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Counit compatibility in equivalence coordinates

Source: Mathlib.CategoryTheory.Adjunction.Mates, `conjugateEquiv_counit`;
Stacks Project, Tag 08HY, the counit description of base change.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

/-- Generic counit compatibility for conjugate adjunctions and equivalence coordinates. -/
theorem coordinate_counit_compatibility
    {A B A0 B0 : Type*} [Category A] [Category B] [Category A0] [Category B0]
    (F : B ⥤ A) (R : A ⥤ B) (F0 : B0 ⥤ A0) (R0 : A0 ⥤ B0)
    (U : A ⥤ A0) (V : A0 ⥤ A) (W : B ⥤ B0) (T : B0 ⥤ B)
    (adj : F ⊣ R) (adj0 : F0 ⊣ R0) (adju : U ⊣ V) (adjt : W ⊣ T)
    (u : 𝟭 A ≅ U ⋙ V) (s : 𝟭 B ≅ W ⋙ T)
    (hu : adju.unit = u.hom) (hs : adjt.unit = s.hom)
    (a : W ⋙ F0 ≅ F ⋙ U)
    (v : T ⋙ F ≅ F0 ⋙ V)
    (e : ∀ K : A, V.obj (U.obj K) ⟶ K)
    (t : ∀ M : B, T.obj (W.obj M) ⟶ M)
    (he : ∀ K : A, e K = u.inv.app K)
    (ht : ∀ M : B, t M = s.inv.app M)
    (hc : ∀ M : B, v.hom.app (W.obj M) ≫
      V.map (a.hom.app M) ≫ e (F.obj M) = F.map (t M))
    (b : R ≅ U ⋙ R0 ⋙ T)
    (hb : ∀ K : A, b.hom.app K = R.map (u.hom.app K) ≫
      (conjugateIsoEquiv (adj.comp adju)
        (adjt.comp adj0) a).hom.app (U.obj K))
    (K : A) :
    F.map (b.hom.app K) ≫
      v.hom.app (R0.obj (U.obj K)) ≫
      V.map (adj0.counit.app (U.obj K)) ≫ e K =
      adj.counit.app K := by
  rw [he, hb K]
  have hc' : ∀ M : B, v.hom.app (W.obj M) ≫
      V.map (a.hom.app M) ≫ u.inv.app (F.obj M) = F.map (s.inv.app M) := by
    intro M
    simpa only [he, ht] using hc M
  let d := (conjugateIsoEquiv (adj.comp adju)
    (adjt.comp adj0) a).hom.app (U.obj K)
  let M := R.obj (V.obj (U.obj K))
  let N := R0.obj (U.obj K)
  have h := conjugateEquiv_counit (adj.comp adju)
    (adjt.comp adj0) a.hom (U.obj K)
  simp only [Adjunction.comp_counit_app, Functor.comp_map] at h
  change F0.map (W.map d) ≫ F0.map (adjt.counit.app N) ≫
    adj0.counit.app (U.obj K) =
    a.hom.app M ≫ U.map (adj.counit.app (V.obj (U.obj K))) ≫
      adju.counit.app (U.obj K) at h
  have hd : s.hom.app M ≫ T.map (W.map d) ≫
      T.map (adjt.counit.app N) = d := by
    have hn := s.hom.naturality d
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    change d ≫ s.hom.app (T.obj N) ≫ T.map (adjt.counit.app N) = d
    rw [← hs]
    rw [adjt.right_triangle_components]
    exact Category.comp_id d
  have hv : F.map d ≫ v.hom.app N ≫
      V.map (adj0.counit.app (U.obj K)) ≫ u.inv.app K =
      adj.counit.app (V.obj (U.obj K)) ≫ u.inv.app K := by
    calc
      _ = F.map (s.hom.app M) ≫ v.hom.app (W.obj M) ≫
          V.map (F0.map (W.map d) ≫ F0.map (adjt.counit.app N) ≫
            adj0.counit.app (U.obj K)) ≫ u.inv.app K := by
        simp only [Functor.map_comp, Category.assoc]
        have hv1 := v.hom.naturality (W.map d)
        have hv2 := v.hom.naturality (adjt.counit.app N)
        dsimp only [Functor.comp_map] at hv1 hv2
        rw [← reassoc_of% hv1, ← reassoc_of% hv2]
        rw [← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, hd]
      _ = _ := by
        rw [h]
        simp only [Functor.map_comp, Category.assoc]
        have ht : V.map (adju.counit.app (U.obj K)) =
            u.inv.app (V.obj (U.obj K)) := by
          apply (cancel_epi (u.hom.app (V.obj (U.obj K)))).mp
          rw [← hu, adju.right_triangle_components, hu, u.hom_inv_id_app]
          rfl
        rw [ht]
        have hn := u.inv.naturality (adj.counit.app (V.obj (U.obj K)))
        dsimp only [Functor.comp_map, Functor.id_map] at hn
        rw [reassoc_of% hn]
        rw [reassoc_of% (hc' M)]
        rw [← F.map_comp_assoc]
        change F.map (s.hom.app M ≫ s.inv.app M) ≫ _ = _
        rw [s.hom_inv_id_app, F.map_id, Category.id_comp]
  change F.map (R.map (u.hom.app K) ≫ d) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, hv]
  have hn := adj.counit.naturality (u.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [reassoc_of% hn]
  simp
