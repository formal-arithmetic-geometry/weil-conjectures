/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent

/-!
# Descent of finite diagrams of étale schemes to a stage of a cofiltered limit

Let `D` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps and limit cone `c`. For functors `F G : K ⥤ Over (D.obj i)` out of a finite
category `K` with quasi-compact quasi-separated étale values we show:

* natural transformations between the base changes of `F` and `G` to the limit descend to a
  stage (`AlgebraicGeometry.exists_overPullback_natTrans`);
* equalities of natural transformations descend to a stage
  (`AlgebraicGeometry.exists_overPullback_whiskerRight_eq`).

We also record the compatibility of the comparison isomorphisms
`AlgebraicGeometry.overPullbackStageIso` with composition of transition maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option linter.flexible false in
lemma overPullbackComp_eqToHom_hom_app_left_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (f' : X ⟶ Z) (hf : f' = f ≫ g) (U : Over Z) :
    ((eqToHom (congrArg (fun k : X ⟶ Z ↦ Over.pullback k) hf)).app U ≫
        (Over.pullbackComp f g).hom.app U).left ≫ pullback.fst _ f ≫ pullback.fst U.hom g =
      pullback.fst U.hom f' := by
  subst hf
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp]
  have hinv : ((Over.pullbackComp f g).inv.app U).left ≫ pullback.fst U.hom (f ≫ g) =
      pullback.fst _ f ≫ pullback.fst U.hom g := by
    simp [Over.pullbackComp, Over.mapComp, conjugateIsoEquiv, conjugateEquiv]
    exact Category.id_comp (pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g)
  rw [← hinv, ← Category.assoc, ← Over.comp_left, Iso.hom_inv_id_app, Over.id_left,
    Category.id_comp]

section Transition

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Base change along a composite of transition maps is the composite of the base changes. -/
noncomputable def overPullbackTransIso {i j k : I} (h : j ⟶ i) (g : k ⟶ j) :
    Over.pullback (D.map (g ≫ h)) ≅ Over.pullback (D.map h) ⋙ Over.pullback (D.map g) :=
  eqToIso (congrArg (fun f ↦ Over.pullback f) (D.map_comp g h)) ≪≫ Over.pullbackComp _ _

@[reassoc (attr := simp)]
lemma overPullbackTransIso_hom_app_left_fst {i j k : I} (h : j ⟶ i) (g : k ⟶ j)
    (U : Over (D.obj i)) :
    ((overPullbackTransIso D h g).hom.app U).left ≫ pullback.fst _ (D.map g) ≫
        pullback.fst U.hom (D.map h) = pullback.fst U.hom (D.map (g ≫ h)) :=
  overPullbackComp_eqToHom_hom_app_left_fst _ _ _ (D.map_comp g h) U

lemma overPullbackStageIso_comp_hom_app {i j k : I} (h : j ⟶ i) (g : k ⟶ j)
    (U : Over (D.obj i)) :
    (overPullbackStageIso D c (g ≫ h)).hom.app U =
      (Over.pullback (c.π.app k)).map ((overPullbackTransIso D h g).hom.app U) ≫
        (overPullbackStageIso D c g).hom.app ((Over.pullback (D.map h)).obj U) ≫
          (overPullbackStageIso D c h).hom.app U := by
  ext1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, overPullbackStageIso_hom_app_left_fst,
      overPullbackStageIso_hom_app_left_fst_assoc, Over.pullback_map_left,
      pullback.lift_fst_assoc, overPullbackTransIso_hom_app_left_fst]
  · simp only [Over.comp_left, Category.assoc, overPullbackStageIso_hom_app_left_snd,
      Over.pullback_map_left, pullback.lift_snd]

end Transition

section Finite

instance SimplexCategory.Truncated.finite (r : ℕ) : Finite (SimplexCategory.Truncated r) := by
  refine Finite.of_injective
    (fun Δ ↦ (⟨Δ.obj.len, Nat.lt_succ_of_le Δ.property⟩ : Fin (r + 1))) ?_
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have : a.len = b.len := congrArg Fin.val hab
  obtain rfl : a = b := this
  rfl

instance SimplexCategory.Truncated.finite_hom {r : ℕ} (a b : SimplexCategory.Truncated r) :
    Finite (a ⟶ b) :=
  Finite.of_injective (fun f ↦ f.hom) fun _ _ h ↦ InducedCategory.hom_ext h

instance Opposite.finite' {K : Type*} [Finite K] : Finite Kᵒᵖ :=
  Finite.of_equiv _ Opposite.equivToOpposite

instance Opposite.finite_hom {K : Type*} [Category K] [∀ a b : K, Finite (a ⟶ b)]
    (a b : Kᵒᵖ) : Finite (a ⟶ b) :=
  Finite.of_injective (fun f ↦ f.unop) fun _ _ h ↦ Quiver.Hom.unop_inj h

end Finite

section Descent

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Equalities between natural transformations of finite diagrams of qcqs étale schemes over a
stage, which hold after base change to the limit, hold at a later stage. -/
theorem exists_overPullback_whiskerRight_eq {K : Type*} [Category K] [Finite K] {i : I}
    (F G : K ⥤ Over (D.obj i)) (hF : ∀ a, IsQcqsEtale (F.obj a))
    (hG : ∀ a, IsQcqsEtale (G.obj a)) (φ ψ : F ⟶ G)
    (hφψ : Functor.whiskerRight φ (Over.pullback (c.π.app i)) =
      Functor.whiskerRight ψ (Over.pullback (c.π.app i))) :
    ∃ (j : I) (h : j ⟶ i), Functor.whiskerRight φ (Over.pullback (D.map h)) =
      Functor.whiskerRight ψ (Over.pullback (D.map h)) := by
  have hev : StageEventually i (fun _ h ↦ ∀ a,
      (Over.pullback (D.map h)).map (φ.app a) = (Over.pullback (D.map h)).map (ψ.app a)) :=
    StageEventually.finite_forall fun a ↦ by
      obtain ⟨_, _, _, _⟩ := hF a
      obtain ⟨_, _, _, _⟩ := hG a
      exact stageEventually_overPullback_map_eq D hc _ _ _ _
        (by simpa using congr_app hφψ a)
  obtain ⟨j, h, hh⟩ := hev.exists_hom
  exact ⟨j, h, NatTrans.ext (funext fun a ↦ by simpa using hh a)⟩

include hc in
/-- Natural transformations between the base changes to the limit of finite diagrams of qcqs
étale schemes over a stage descend to a later stage. -/
theorem exists_overPullback_natTrans {K : Type*} [Category K] [Finite K]
    [∀ a b : K, Finite (a ⟶ b)] {i : I}
    (F G : K ⥤ Over (D.obj i)) (hF : ∀ a, IsQcqsEtale (F.obj a))
    (hG : ∀ a, IsQcqsEtale (G.obj a))
    (φ : F ⋙ Over.pullback (c.π.app i) ⟶ G ⋙ Over.pullback (c.π.app i)) :
    ∃ (j : I) (h : j ⟶ i) (ψ : F ⋙ Over.pullback (D.map h) ⟶ G ⋙ Over.pullback (D.map h)),
      ∀ a, (Over.pullback (c.π.app j)).map (ψ.app a) ≫
          (overPullbackStageIso D c h).hom.app (G.obj a) =
        (overPullbackStageIso D c h).hom.app (F.obj a) ≫ φ.app a := by
  -- descend the components
  have hev : StageEventually i (fun j h ↦ ∀ a, ∃ ψ : (Over.pullback (D.map h)).obj (F.obj a) ⟶
      (Over.pullback (D.map h)).obj (G.obj a),
      (Over.pullback (c.π.app j)).map ψ ≫ (overPullbackStageIso D c h).hom.app (G.obj a) =
        (overPullbackStageIso D c h).hom.app (F.obj a) ≫ φ.app a) :=
    StageEventually.finite_forall fun a ↦ by
      obtain ⟨_, _, _, _⟩ := hF a
      obtain ⟨_, _, _, _⟩ := hG a
      exact stageEventually_exists_overPullback_hom D hc _ _ (φ.app a)
  obtain ⟨j, h, hh⟩ := hev.exists_hom
  choose ψ₀ hψ₀ using hh
  let S := overPullbackStageIso D c h
  -- naturality holds after base change to the limit
  have hnat : ∀ x : Σ a b : K, a ⟶ b,
      (Over.pullback (c.π.app j)).map ((Over.pullback (D.map h)).map (F.map x.2.2) ≫
          ψ₀ x.2.1) =
        (Over.pullback (c.π.app j)).map (ψ₀ x.1 ≫
          (Over.pullback (D.map h)).map (G.map x.2.2)) := by
    rintro ⟨a, b, f⟩
    rw [← cancel_mono (S.hom.app (G.obj b))]
    have h1 := S.hom.naturality (F.map f)
    have h2 := S.hom.naturality (G.map f)
    have h3 := φ.naturality f
    simp only [Functor.comp_map] at h1 h2 h3
    simp only [Functor.map_comp, Category.assoc]
    rw [hψ₀ b, reassoc_of% h1, h2, reassoc_of% hψ₀ a, h3]
  have hev₂ : StageEventually j (fun _ g ↦ ∀ x : Σ a b : K, a ⟶ b,
      (Over.pullback (D.map g)).map ((Over.pullback (D.map h)).map (F.map x.2.2) ≫
          ψ₀ x.2.1) =
        (Over.pullback (D.map g)).map (ψ₀ x.1 ≫
          (Over.pullback (D.map h)).map (G.map x.2.2))) :=
    StageEventually.finite_forall fun x ↦ by
      obtain ⟨_, _, _, _⟩ := (hF x.1).overPullback (D.map h)
      obtain ⟨_, _, _, _⟩ := (hG x.2.1).overPullback (D.map h)
      exact stageEventually_overPullback_map_eq D hc _ _ _ _ (hnat x)
  obtain ⟨k, g, hg⟩ := hev₂.exists_hom
  let T := overPullbackTransIso D h g
  refine ⟨k, g ≫ h,
    { app := fun a ↦ T.hom.app (F.obj a) ≫ (Over.pullback (D.map g)).map (ψ₀ a) ≫
        T.inv.app (G.obj a)
      naturality := fun a b f ↦ ?_ }, fun a ↦ ?_⟩
  · have h1 := T.hom.naturality (F.map f)
    have h2 := T.inv.naturality (G.map f)
    have h3 := hg ⟨a, b, f⟩
    simp only [Functor.comp_map] at h1 h2 ⊢
    rw [Functor.map_comp, Functor.map_comp] at h3
    simp only [Category.assoc]
    rw [reassoc_of% h1, reassoc_of% h3, h2]
  · simp only [overPullbackStageIso_comp_hom_app, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (Over.pullback (c.π.app k)) (T.inv.app (G.obj a)),
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    have h1 := (overPullbackStageIso D c g).hom.naturality (ψ₀ a)
    simp only [Functor.comp_map] at h1
    rw [reassoc_of% h1, hψ₀ a]

end Descent

end AlgebraicGeometry
