/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Sheaf.CategoryTheory.Sites.InverseImageUnderlyingAdjunction

/-!
# Bilinear adjunction for inverse images of sites

Source: Stacks Project, Tag 03EL, lemma-tensor-product-pullback, third equality;
Sites, Section 00YR and Proposition 00YV(2)
(blueprint: lem-sfb-site-inverse-image-bilinear-adjunction).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁ u₂ v₂

namespace CategoryTheory

/-- A morphism of underlying sheaves of sets that is separately additive on sections.

The `natural` field is naturality of a map from the sectionwise product; it does
not require additivity for the abelian group structure on that product.
Source: Stacks Project, Tag 03EL, definition before lemma-tensor-product-pullback
(blueprint: lem-sfb-site-inverse-image-bilinear-adjunction). -/
structure SiteBilinearMap {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F G H : Sheaf J AddCommGrpCat.{w}) where
  /-- The sectionwise two-variable map. -/
  app : ∀ U : C, F.obj.obj (Opposite.op U) → G.obj.obj (Opposite.op U) →
    H.obj.obj (Opposite.op U)
  /-- Compatibility with restriction of sections. -/
  natural : ∀ {U V : C} (f : U ⟶ V) (x : F.obj.obj (Opposite.op V))
    (y : G.obj.obj (Opposite.op V)),
    app U (F.obj.map f.op x) (G.obj.map f.op y) = H.obj.map f.op (app V x y)
  /-- Additivity in the first variable. -/
  add_left : ∀ (U : C) (x₁ x₂ : F.obj.obj (Opposite.op U)) (y : G.obj.obj (Opposite.op U)),
    app U (x₁ + x₂) y = app U x₁ y + app U x₂ y
  /-- Additivity in the second variable. -/
  add_right : ∀ (U : C) (x : F.obj.obj (Opposite.op U)) (y₁ y₂ : G.obj.obj (Opposite.op U)),
    app U x (y₁ + y₂) = app U x y₁ + app U x y₂

/-- The sectionwise unit of the canonical site inverse-image/direct-image adjunction.

Source: Stacks Project, Sites, Section 00YR and Proposition 00YV(2)
(blueprint: lem-sfb-site-inverse-image-bilinear-adjunction). -/
noncomputable def siteAdjunctionUnitSection
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    (F : Sheaf J AddCommGrpCat.{w}) (U : C) :
    F.obj.obj (Opposite.op U) →
      ((u.sheafPullback AddCommGrpCat.{w} J K).obj F).obj.obj
        (Opposite.op (u.obj U)) :=
  fun x ↦ ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app
    (Opposite.op U) x

section

set_option backward.isDefEq.respectTransparency false

private noncomputable def bilinearTranspose
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    (F G : Sheaf J AddCommGrpCat.{w}) (H : Sheaf K AddCommGrpCat.{w})
    (β : SiteBilinearMap ((u.sheafPullback AddCommGrpCat.{w} J K).obj F)
      ((u.sheafPullback AddCommGrpCat.{w} J K).obj G) H) :
    SiteBilinearMap F G ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj H) where
  app U x y := β.app (u.obj U)
    (siteAdjunctionUnitSection J K u F U x) (siteAdjunctionUnitSection J K u G U y)
  natural {U V} f x y := by
    have hF := NatTrans.naturality
      ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom f.op
    have hG := NatTrans.naturality
      ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app G).hom f.op
    have hFx := ConcreteCategory.congr_hom hF x
    have hGy := ConcreteCategory.congr_hom hG y
    change siteAdjunctionUnitSection J K u F U (F.obj.map f.op x) =
      _ at hFx
    change siteAdjunctionUnitSection J K u G U (G.obj.map f.op y) =
      _ at hGy
    rw [hFx, hGy]
    exact β.natural (u.map f) _ _
  add_left U x₁ x₂ y := by
    change β.app _ (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app
      (Opposite.op U) (x₁ + x₂)) _ = _
    rw [map_add]
    exact β.add_left _ _ _ _
  add_right U x y₁ y₂ := by
    change β.app _ _ (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app G).hom.app
      (Opposite.op U) (y₁ + y₂)) = _
    rw [map_add]
    exact β.add_right _ _ _ _

private theorem multimap_ext
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {n : ℕ} {F : Fin n → Sheaf J AddCommGrpCat.{w}}
    {H : Sheaf J AddCommGrpCat.{w}} {a b : SiteSectionMultimap F H}
    (h : ∀ U x, a.app U x = b.app U x) : a = b := by
  cases a
  cases b
  congr
  funext U _x
  exact h U _x

private theorem bilinear_ext
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {F G H : Sheaf J AddCommGrpCat.{w}} {a b : SiteBilinearMap F G H}
    (h : ∀ U x y, a.app U x y = b.app U x y) : a = b := by
  cases a
  cases b
  congr
  funext U x y
  exact h U x y

private def bilinearToMultimap
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {F G H : Sheaf J AddCommGrpCat.{w}} (b : SiteBilinearMap F G H) :
    SiteSectionMultimap ![F, G] H where
  app U x := b.app U (x 0) (x 1)
  natural f _x := b.natural f _ _

private noncomputable def multimapTranspose
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    {n : ℕ} (F : Fin n → Sheaf J AddCommGrpCat.{w})
    (H : Sheaf K AddCommGrpCat.{w})
    (b : SiteSectionMultimap (fun i ↦ (u.sheafPullback AddCommGrpCat.{w} J K).obj (F i)) H) :
    SiteSectionMultimap F ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj H) where
  app U x := b.app (u.obj U) (fun i ↦ siteAdjunctionUnitSection J K u (F i) U (x i))
  natural {U V} f x := by
    have h (i : Fin n) := ConcreteCategory.congr_hom
      (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app (F i)).hom.naturality
        f.op) (x i)
    change (∀ i, siteAdjunctionUnitSection J K u (F i) U ((F i).obj.map f.op (x i)) =
      ((u.sheafPullback AddCommGrpCat.{w} J K).obj (F i)).obj.map (u.map f).op
        (siteAdjunctionUnitSection J K u (F i) V (x i))) at h
    change b.app (u.obj U) _ = _
    simp only [h]
    exact b.natural (u.map f) _

private theorem multimap_unit_injective
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).IsRightAdjoint]
    [PreservesFiniteLimits (u.sheafPullback (Type (max u₁ v₁ u₂ v₂ w)) J K)]
    {n : ℕ} (F : Fin n → Sheaf J AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
    (H : Sheaf K AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
    (a b : SiteSectionMultimap
      (fun i ↦ (u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).obj (F i)) H)
    (h : ∀ (U : C) (x : ∀ i, (F i).obj.obj (Opposite.op U)),
      a.app (u.obj U) (fun i ↦ siteAdjunctionUnitSection J K u (F i) U (x i)) =
      b.app (u.obj U) (fun i ↦ siteAdjunctionUnitSection J K u (F i) U (x i))) : a = b := by
  obtain ⟨c, _, hc⟩ := site_inverse_image_multimap_universal J K u F H
    (multimapTranspose J K u F H b)
  exact (hc a h).trans (hc b (fun _ _ ↦ rfl)).symm

section RawMaps

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {F G H : Sheaf J AddCommGrpCat.{w}}

private def pairSections (U : C)
    (x : F.obj.obj (Opposite.op U)) (y : G.obj.obj (Opposite.op U)) :
    ∀ i, (![F, G] i).obj.obj (Opposite.op U) :=
  Fin.cases x (Fin.cases y (fun i ↦ Fin.elim0 i))

@[simp] private theorem pairSections_zero (U : C)
    (x : F.obj.obj (Opposite.op U)) (y : G.obj.obj (Opposite.op U)) :
    pairSections U x y 0 = x := rfl

@[simp] private theorem pairSections_one (U : C)
    (x : F.obj.obj (Opposite.op U)) (y : G.obj.obj (Opposite.op U)) :
    pairSections U x y 1 = y := rfl

private theorem pairSections_map {U V : C} (f : U ⟶ V)
    (x : F.obj.obj (Opposite.op V)) (y : G.obj.obj (Opposite.op V)) :
    (fun i ↦ (![F, G] i).obj.map f.op (pairSections V x y i)) =
      pairSections U (F.obj.map f.op x) (G.obj.map f.op y) := by
  funext i
  fin_cases i <;> rfl

private def rawAddLeft (b : SiteSectionMultimap ![F, G] H) :
    SiteSectionMultimap ![F, F, G] H where
  app U x := b.app U (pairSections U
    ((show F.obj.obj (Opposite.op U) from x 0) +
      (show F.obj.obj (Opposite.op U) from x 1)) (x 2))
  natural {U V} f x := by
    change b.app U (pairSections U (F.obj.map f.op (x 0) + F.obj.map f.op (x 1))
      (G.obj.map f.op (x 2))) = _
    rw [← map_add]
    exact (by simpa [pairSections_map] using
      b.natural f (pairSections V
        ((show F.obj.obj (Opposite.op V) from x 0) +
          (show F.obj.obj (Opposite.op V) from x 1)) (x 2)))

private def rawSumLeft (b : SiteSectionMultimap ![F, G] H) :
    SiteSectionMultimap ![F, F, G] H where
  app U x := b.app U (pairSections U (x 0) (x 2)) +
    b.app U (pairSections U (x 1) (x 2))
  natural f x := by
    rw [map_add]
    exact congrArg₂ (· + ·)
      (by simpa [pairSections_map] using b.natural f (pairSections _ (x 0) (x 2)))
      (by simpa [pairSections_map] using b.natural f (pairSections _ (x 1) (x 2)))

private def rawAddRight (b : SiteSectionMultimap ![F, G] H) :
    SiteSectionMultimap ![F, G, G] H where
  app U x := b.app U (pairSections U (x 0)
    ((show G.obj.obj (Opposite.op U) from x 1) +
      (show G.obj.obj (Opposite.op U) from x 2)))
  natural {U V} f x := by
    change b.app U (pairSections U (F.obj.map f.op (x 0))
      (G.obj.map f.op (x 1) + G.obj.map f.op (x 2))) = _
    rw [← map_add]
    exact (by simpa [pairSections_map] using
      b.natural f (pairSections V (x 0)
        ((show G.obj.obj (Opposite.op V) from x 1) +
          (show G.obj.obj (Opposite.op V) from x 2))))

private def rawSumRight (b : SiteSectionMultimap ![F, G] H) :
    SiteSectionMultimap ![F, G, G] H where
  app U x := b.app U (pairSections U (x 0) (x 1)) +
    b.app U (pairSections U (x 0) (x 2))
  natural f x := by
    rw [map_add]
    exact congrArg₂ (· + ·)
      (by simpa [pairSections_map] using b.natural f (pairSections _ (x 0) (x 1)))
      (by simpa [pairSections_map] using b.natural f (pairSections _ (x 0) (x 2)))

end RawMaps

@[simp] private theorem eqToHom_section_cancel
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {A B : Sheaf J AddCommGrpCat.{w}} (h : A = B) (U : C)
    (x : B.obj.obj (Opposite.op U)) :
    ((eqToHom h).hom.app (Opposite.op U))
      (((eqToHom h.symm).hom.app (Opposite.op U)) x) = x := by
  subst B
  rfl

private def repackMultimap
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {n : ℕ} {F G : Fin n → Sheaf J AddCommGrpCat.{w}}
    {H : Sheaf J AddCommGrpCat.{w}} (h : ∀ i, F i = G i)
    (b : SiteSectionMultimap F H) : SiteSectionMultimap G H where
  app U x := b.app U (fun i ↦ ((eqToHom (h i).symm).hom.app (Opposite.op U)) (x i))
  natural {U V} f x := by
    have he (i : Fin n) := ConcreteCategory.congr_hom
      ((eqToHom (h i).symm).hom.naturality f.op) (x i)
    have ht : (fun i ↦ ((eqToHom (h i).symm).hom.app (Opposite.op U))
        ((G i).obj.map f.op (x i))) =
        (fun i ↦ (F i).obj.map f.op
          (((eqToHom (h i).symm).hom.app (Opposite.op V)) (x i))) := by
      funext i
      exact he i
    change b.app U _ = _
    rw [ht]
    exact b.natural f _

private theorem bilinearTranspose_bijective
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).IsRightAdjoint]
    [PreservesFiniteLimits (u.sheafPullback (Type (max u₁ v₁ u₂ v₂ w)) J K)]
    (F G : Sheaf J AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
    (H : Sheaf K AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}) :
    Function.Bijective (bilinearTranspose J K u F G H) := by
  let L := u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K
  have h2 : (fun i ↦ L.obj (![F, G] i)) = ![L.obj F, L.obj G] := by
    funext i
    fin_cases i <;> rfl
  have h3l : (fun i ↦ L.obj (![F, F, G] i)) = ![L.obj F, L.obj F, L.obj G] := by
    funext i
    fin_cases i <;> rfl
  have h3r : (fun i ↦ L.obj (![F, G, G] i)) = ![L.obj F, L.obj G, L.obj G] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro a b h
    have hr : bilinearToMultimap a = bilinearToMultimap b := by
      have hi := multimap_unit_injective J K u ![F, G] H
      let a' := repackMultimap (fun i ↦ congrFun h2.symm i) (bilinearToMultimap a)
      let b' := repackMultimap (fun i ↦ congrFun h2.symm i) (bilinearToMultimap b)
      have he : a' = b' := hi a' b' (by
        intro U x
        simpa [a', b', repackMultimap, bilinearToMultimap, bilinearTranspose] using
          congrArg (fun b ↦ b.app U (x 0) (x 1)) h)
      apply multimap_ext
      intro V x
      have he' := congrArg (fun t ↦ t.app V
        (fun i ↦ ((eqToHom (congrFun h2 i).symm).hom.app (Opposite.op V)) (x i))) he
      simpa only [a', b', repackMultimap, eqToHom_section_cancel] using he'
    apply bilinear_ext
    intro V x y
    simpa [bilinearToMultimap] using
      congrArg (fun b ↦ b.app V (pairSections V x y)) hr
  · intro b
    have hu := site_inverse_image_multimap_universal J K u ![F, G] H
      (bilinearToMultimap b)
    obtain ⟨β₀, hβ, _⟩ := hu
    let β := repackMultimap (fun i ↦ congrFun h2 i) β₀
    have heval (U : C) (x : F.obj.obj (Opposite.op U))
        (y : G.obj.obj (Opposite.op U)) :
        β.app (u.obj U)
          (pairSections _ (siteAdjunctionUnitSection J K u F U x)
            (siteAdjunctionUnitSection J K u G U y)) = b.app U x y := by
      have ht : (fun i ↦ ((eqToHom (congrFun h2 i).symm).hom.app
          (Opposite.op (u.obj U)))
          (pairSections _ (siteAdjunctionUnitSection J K u F U x)
            (siteAdjunctionUnitSection J K u G U y) i)) =
          (fun i ↦ siteAdjunctionUnitSection J K u (![F, G] i) U
            (pairSections U x y i)) := by
        funext i
        fin_cases i <;> rfl
      change β₀.app _ _ = _
      rw [ht]
      simpa [bilinearToMultimap, siteAdjunctionUnitSection] using
        hβ U (pairSections U x y)
    have hleft : rawAddLeft β = rawSumLeft β := by
      have hi := multimap_unit_injective J K u ![F, F, G] H
      have he : repackMultimap (fun i ↦ congrFun h3l.symm i) (rawAddLeft β) =
          repackMultimap (fun i ↦ congrFun h3l.symm i) (rawSumLeft β) := by
        apply hi
        intro U x
        change β.app _ (pairSections _
          (siteAdjunctionUnitSection J K u F U (x 0) +
            siteAdjunctionUnitSection J K u F U (x 1))
          (siteAdjunctionUnitSection J K u G U (x 2))) = _
        have hadd : siteAdjunctionUnitSection J K u F U ((show F.obj.obj (Opposite.op U) from x 0) +
            (show F.obj.obj (Opposite.op U) from x 1)) =
            siteAdjunctionUnitSection J K u F U (x 0) +
              siteAdjunctionUnitSection J K u F U (x 1) := map_add _ _ _
        rw [← hadd, heval]
        change _ = β.app _ (pairSections _
          (siteAdjunctionUnitSection J K u F U (x 0))
          (siteAdjunctionUnitSection J K u G U (x 2))) +
          β.app _ (pairSections _ (siteAdjunctionUnitSection J K u F U (x 1))
            (siteAdjunctionUnitSection J K u G U (x 2)))
        rw [heval, heval]
        exact b.add_left _ _ _ _
      apply multimap_ext
      intro V x
      have he' := congrArg (fun t ↦ t.app V
        (fun i ↦ ((eqToHom (congrFun h3l i).symm).hom.app (Opposite.op V)) (x i))) he
      simpa only [repackMultimap, eqToHom_section_cancel] using he'
    have hright : rawAddRight β = rawSumRight β := by
      have hi := multimap_unit_injective J K u ![F, G, G] H
      have he : repackMultimap (fun i ↦ congrFun h3r.symm i) (rawAddRight β) =
          repackMultimap (fun i ↦ congrFun h3r.symm i) (rawSumRight β) := by
        apply hi
        intro U x
        change β.app _ (pairSections _ (siteAdjunctionUnitSection J K u F U (x 0))
          (siteAdjunctionUnitSection J K u G U (x 1) +
            siteAdjunctionUnitSection J K u G U (x 2))) = _
        have hadd : siteAdjunctionUnitSection J K u G U ((show G.obj.obj (Opposite.op U) from x 1) +
            (show G.obj.obj (Opposite.op U) from x 2)) =
            siteAdjunctionUnitSection J K u G U (x 1) +
              siteAdjunctionUnitSection J K u G U (x 2) := map_add _ _ _
        rw [← hadd, heval]
        change _ = β.app _ (pairSections _ (siteAdjunctionUnitSection J K u F U (x 0))
          (siteAdjunctionUnitSection J K u G U (x 1))) +
          β.app _ (pairSections _ (siteAdjunctionUnitSection J K u F U (x 0))
            (siteAdjunctionUnitSection J K u G U (x 2)))
        rw [heval, heval]
        exact b.add_right _ _ _ _
      apply multimap_ext
      intro V x
      have he' := congrArg (fun t ↦ t.app V
        (fun i ↦ ((eqToHom (congrFun h3r i).symm).hom.app (Opposite.op V)) (x i))) he
      simpa only [repackMultimap, eqToHom_section_cancel] using he'
    let βb : SiteBilinearMap
        ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).obj F)
        ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w} J K).obj G) H := {
      app := fun V x y ↦ β.app V (pairSections V x y)
      natural := by
        intro U V f x y
        simpa [pairSections_map] using β.natural f (pairSections V x y)
      add_left := by
        intro V x₁ x₂ y
        exact congrArg (fun t ↦ t.app V (Fin.cases x₁
          (Fin.cases x₂ (Fin.cases y (fun i ↦ Fin.elim0 i))))) hleft
      add_right := by
        intro V x y₁ y₂
        exact congrArg (fun t ↦ t.app V (Fin.cases x
          (Fin.cases y₁ (Fin.cases y₂ (fun i ↦ Fin.elim0 i))))) hright }
    refine ⟨βb, ?_⟩
    apply bilinear_ext
    exact heval

end

set_option linter.unusedVariables false in
/-- The two-unit formula is a natural bijection on separately additive sheaf maps.

The precoverages satisfy the recorded site axioms. `hcover` and `hpullback` are
Stacks continuity; `IsContinuous` is the induced sheaf-preservation property used
by Mathlib's interface. Finite limits are preserved on sheaves of sets. Values
lie in the common universe containing both sites, with no equality imposed on
their object and morphism universes. The last clause expresses naturality: whenever
`β₀ = h ∘ β₁ ∘ (L a × L c)` on sections, the same equation holds after transposition,
with `a`, `c` and `R h`. Sectionwise equality determines these underlying sheaf maps.

Source: Stacks Project, Tag 03EL, third equality in lemma-tensor-product-pullback
(blueprint: lem-sfb-site-inverse-image-bilinear-adjunction).

Proof:
1. The size convention def-weil-size-convention supplies the common value universe.
   By def-weil-pbc-sites-and-cohomology, R is restriction and preserves finite
   products. Identify abelian sheaves with commutative group objects using
   lem-weil-pbc-sheaf-algebraic-structures-objects. Lift L ⊣ R using
   lem-weil-pbc-adjunction-lifts-abelian-group-objects: its multiplication is
   L(+) after the inverse product comparison, and unit and counit are additive.
2. For underlying set maps use the ordinary adjunction after the product
   comparison λ : L(F × G) ≅ LF × LG. The forward map is R(βλ)η, and the
   inverse is ε L(b)λ⁻¹. Naturality of η with both projections identifies the
   forward map with R(β) after the two units and the inverse R-product comparison.
3. The two units are additive, so the forward map preserves separate additivity
   by expanding β(η(x + x'), η(y)) and β(η(x), η(y + y')).
4. Express the two additivity laws for b as equalities of maps from F × F × G
   and F × G × G. Apply L and identify all products by λ. Comparing projections
   shows λ L⟨q,r⟩ = ⟨Lq,Lr⟩; the resulting identities are the two additivity
   laws of L(b)λ⁻¹. Preservation of zero and negatives follows by cancellation.
5. Postcompose with the additive counit. Both directions are now separately
   additive and are inverse by counit naturality and the two triangle identities.
6. For a, c and h, functoriality of R and unit naturality give the displayed
   naturality equality, contravariantly in F,G and covariantly in H. -/
theorem site_inverse_image_bilinear_adjunction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (u : C ⥤ D)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map u ∈ K (u.obj X))
    (hpullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) u)
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
      J.toGrothendieck K.toGrothendieck).IsRightAdjoint]
    [PreservesFiniteLimits
      (u.sheafPullback (Type (max u₁ v₁ u₂ v₂ w)) J.toGrothendieck K.toGrothendieck)] :
    ∃ e : ∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}),
        SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G) H →
        SiteBilinearMap F G
          ((u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj H),
      (∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}),
        Function.Bijective (e F G H)) ∧
      (∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (β : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G) H)
        (U : C) (x : F.obj.obj (Opposite.op U)) (y : G.obj.obj (Opposite.op U)),
        (e F G H β).app U x y = β.app (u.obj U)
          (siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u F U x)
          (siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u G U y)) ∧
      (∀ {F₀ F₁ G₀ G₁ : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}}
        {H₀ H₁ : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}}
        (a : F₀ ⟶ F₁) (c : G₀ ⟶ G₁) (h : H₀ ⟶ H₁)
        (β₁ : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₁)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₁) H₀)
        (β₀ : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₀)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₀) H₁),
        (∀ (V : D)
          (x : ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₀).obj.obj (Opposite.op V))
          (y : ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₀).obj.obj (Opposite.op V)),
          β₀.app V x y = h.hom.app (Opposite.op V)
            (β₁.app V
              (((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
                J.toGrothendieck K.toGrothendieck).map a).hom.app (Opposite.op V) x)
              (((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
                J.toGrothendieck K.toGrothendieck).map c).hom.app (Opposite.op V) y))) →
        ∀ (U : C) (x : F₀.obj.obj (Opposite.op U)) (y : G₀.obj.obj (Opposite.op U)),
          (e F₀ G₀ H₁ β₀).app U x y = h.hom.app (Opposite.op (u.obj U))
            ((e F₁ G₁ H₀ β₁).app U
              (a.hom.app (Opposite.op U) x) (c.hom.app (Opposite.op U) y))) := by
  set_option backward.isDefEq.respectTransparency false in
  exact (by
    refine ⟨bilinearTranspose J.toGrothendieck K.toGrothendieck u, ?_, ?_, ?_⟩
    · exact bilinearTranspose_bijective J.toGrothendieck K.toGrothendieck u
    · intro F G H β U x y
      rfl
    · intro F₀ F₁ G₀ G₁ H₀ H₁ a c h β₁ β₀ hβ U x y
      change β₀.app (u.obj U) _ _ = _
      rw [hβ]
      have ha := congrArg (fun t ↦ t.hom.app (Opposite.op U) x)
        ((u.sheafAdjunctionContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
          J.toGrothendieck K.toGrothendieck).unit.naturality a)
      have hc := congrArg (fun t ↦ t.hom.app (Opposite.op U) y)
        ((u.sheafAdjunctionContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
          J.toGrothendieck K.toGrothendieck).unit.naturality c)
      change siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u F₁ U
        (a.hom.app (Opposite.op U) x) = _ at ha
      change siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u G₁ U
        (c.hom.app (Opposite.op U) y) = _ at hc
      change siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u F₁ U
        (a.hom.app (Opposite.op U) x) =
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).map a).hom.app (Opposite.op (u.obj U))
            (siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u F₀ U x) at ha
      change siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u G₁ U
        (c.hom.app (Opposite.op U) y) =
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).map c).hom.app (Opposite.op (u.obj U))
            (siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u G₀ U y) at hc
      change _ = h.hom.app _ (β₁.app _ _ _)
      rw [← ha, ← hc]
  )

end CategoryTheory
