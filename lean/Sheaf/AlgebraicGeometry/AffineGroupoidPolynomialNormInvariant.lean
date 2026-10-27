/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.CategoryTheory.Groupoid
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm

/-!
# Polynomial source norms are invariant under an affine groupoid

Source: Stacks Project, Groupoids, Tag 03BH, `lemma-determinant-trick`, applied after
adjoining a polynomial coordinate as in `lemma-integral-over-invariants`; Exercises,
Tag 02DV(1),(3) (blueprint: lem-a1-affine-groupoid-polynomial-norm-invariant).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

-- Polynomial points are determined by a base point and one global section.
private abbrev polySpec (A : CommRingCat.{u}) : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial A))

private def polyMap {A B : CommRingCat.{u}} (f : Spec B ⟶ Spec A) :
    polySpec B ⟶ polySpec A :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Spec.preimage f).hom))

private def polyBase (A : CommRingCat.{u}) : polySpec A ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

private def pointRing {H : Scheme.{u}} {A : CommRingCat.{u}} (f : H ⟶ Spec A) :
    A ⟶ Γ(H, ⊤) := (Scheme.ΓSpecIso A).inv ≫ f.appTop

private def polyLift {H : Scheme.{u}} {A : CommRingCat.{u}}
    (f : H ⟶ Spec A) (z : Γ(H, ⊤)) : H ⟶ polySpec A :=
  ΓSpec.adjunction.homEquiv H (Opposite.op (CommRingCat.of (Polynomial A)))
    (CommRingCat.ofHom (Polynomial.eval₂RingHom (pointRing f).hom z)).op

private def polyCoord {H : Scheme.{u}} {A : CommRingCat.{u}}
    (f : H ⟶ polySpec A) : Γ(H, ⊤) := pointRing f Polynomial.X

private lemma pointRing_polyLift {H : Scheme.{u}} {A : CommRingCat.{u}}
    (f : H ⟶ Spec A) (z : Γ(H, ⊤)) :
    pointRing (polyLift f z) =
      CommRingCat.ofHom (Polynomial.eval₂RingHom (pointRing f).hom z) := by
  exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

private lemma pointRing_comp {H : Scheme.{u}} {A B : CommRingCat.{u}}
    (f : H ⟶ Spec B) (g : Spec B ⟶ Spec A) :
    pointRing (f ≫ g) = Spec.preimage g ≫ pointRing f := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  simp only [pointRing, Scheme.Hom.comp_appTop, Spec.preimage_map]
  rw [Scheme.ΓSpecIso_inv_naturality_assoc]

private lemma pointRing_injective {H : Scheme.{u}} {A : CommRingCat.{u}} :
    Function.Injective (pointRing (H := H) (A := A)) := by
  intro f g h
  exact ext_to_Spec h

private lemma polyLift_base {H : Scheme.{u}} {A : CommRingCat.{u}}
    (f : H ⟶ Spec A) (z : Γ(H, ⊤)) : polyLift f z ≫ polyBase A = f := by
  apply pointRing_injective
  rw [pointRing_comp, pointRing_polyLift]
  simp only [polyBase, Spec.preimage_map]
  ext a
  exact Polynomial.eval₂_C _ _

private lemma polyLift_coord {H : Scheme.{u}} {A : CommRingCat.{u}}
    (f : H ⟶ Spec A) (z : Γ(H, ⊤)) : polyCoord (polyLift f z) = z := by
  simp only [polyCoord, pointRing_polyLift, CommRingCat.hom_ofHom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

private lemma polyPoint_ext {H : Scheme.{u}} {A : CommRingCat.{u}}
    {f g : H ⟶ polySpec A} (hb : f ≫ polyBase A = g ≫ polyBase A)
    (hz : polyCoord f = polyCoord g) : f = g := by
  apply pointRing_injective
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · have h := congrArg pointRing hb
    rw [pointRing_comp, pointRing_comp] at h
    intro a
    simpa only [polyBase, Spec.preimage_map, CommRingCat.comp_apply,
      CommRingCat.hom_ofHom] using ConcreteCategory.congr_hom h a
  · exact hz

@[reassoc]
private lemma polyMap_base {A B : CommRingCat.{u}} (f : Spec B ⟶ Spec A) :
    polyMap f ≫ polyBase A = polyBase B ≫ f := by
  rw [← Spec.map_preimage f]
  simp only [polyMap, polyBase, Spec.preimage_map, ← Spec.map_comp]
  congr 1
  ext a
  simp

private lemma polyMap_coord {H : Scheme.{u}} {A B : CommRingCat.{u}}
    (g : H ⟶ polySpec B) (f : Spec B ⟶ Spec A) :
    polyCoord (g ≫ polyMap f) = polyCoord g := by
  change pointRing (g ≫ polyMap f) Polynomial.X = pointRing g Polynomial.X
  rw [pointRing_comp]
  simp only [polyMap, Spec.preimage_map]
  change pointRing g (Polynomial.map (Spec.preimage f).hom Polynomial.X) = _
  rw [Polynomial.map_X]

private lemma polyMap_selfcoord {A B : CommRingCat.{u}} (f : Spec B ⟶ Spec A) :
    polyCoord (polyMap f) = polyCoord (𝟙 (polySpec B)) := by
  simpa only [Category.id_comp] using polyMap_coord (𝟙 (polySpec B)) f

private lemma polyMap_finiteLocallyFree {A B : CommRingCat.{u}}
    (f : Spec B ⟶ Spec A) [f.IsFiniteLocallyFree] : (polyMap f).IsFiniteLocallyFree := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hb : IsPullback (polyBase B) (polyMap (Spec.map φ)) (Spec.map φ) (polyBase A) := by
    dsimp only [polyBase, polyMap]
    rw [Spec.preimage_map]
    algebraize [φ.hom, Polynomial.mapRingHom φ.hom]
    exact (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isPushout A B (Polynomial A) (Polynomial B)))
  have : IsFinite (polyMap (Spec.map φ)) := MorphismProperty.of_isPullback hb inferInstance
  have : Flat (polyMap (Spec.map φ)) := MorphismProperty.of_isPullback hb inferInstance
  have : LocallyOfFinitePresentation (polyMap (Spec.map φ)) :=
    MorphismProperty.of_isPullback hb inferInstance
  exact ⟨⟩

-- Recover the scheme laws from the supplied equivalences on test points.
private theorem groupoidLaws_of_points
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R)
    (hgroupoid : ∀ H : Scheme.{u},
      ∃ (G : Groupoid.{u} (H ⟶ U))
        (φ : ∀ x y : H ⟶ U,
          @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y ≃
            {r : H ⟶ R // r ≫ s = x ∧ r ≫ t = y}),
        (∀ x : H ⟶ U,
          (φ x x (@CategoryStruct.id _ G.toCategory.toCategoryStruct x)).val = x ≫ e) ∧
        (∀ (x y : H ⟶ U)
          (f : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y),
          (φ y x (@Groupoid.inv _ G x y f)).val = (φ x y f).val ≫ i) ∧
        (∀ (x y z : H ⟶ U)
          (f : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y)
          (g : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver y z),
          (φ x z (@CategoryStruct.comp _ G.toCategory.toCategoryStruct x y z f g)).val =
            pullback.lift (φ y z g).val (φ x y f).val
              ((φ y z g).property.1.trans (φ x y f).property.2.symm) ≫ c)) :
    Scheme.IsGroupoid s t e i c := by
  classical
  have hid (H : Scheme.{u}) (x : H ⟶ U) :
      (x ≫ e) ≫ s = x ∧ (x ≫ e) ≫ t = x := by
    obtain ⟨G, φ, he, -, -⟩ := hgroupoid H
    rw [← he x]
    exact (φ x x (𝟙 x)).property
  have hinv (H : Scheme.{u}) (a : H ⟶ R) :
      (a ≫ i) ≫ s = a ≫ t ∧ (a ≫ i) ≫ t = a ≫ s := by
    obtain ⟨G, φ, -, hi, -⟩ := hgroupoid H
    let f := (φ (a ≫ s) (a ≫ t)).symm ⟨a, rfl, rfl⟩
    have hf : (φ _ _ f).val = a := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hi' := hi _ _ f
    rw [hf] at hi'
    rw [← hi']
    exact (φ _ _ (Groupoid.inv f)).property
  have hcomp (H : Scheme.{u}) (p : H ⟶ pullback s t) :
      (p ≫ c) ≫ s = (p ≫ pullback.snd s t) ≫ s ∧
      (p ≫ c) ≫ t = (p ≫ pullback.fst s t) ≫ t := by
    obtain ⟨G, φ, -, -, hc⟩ := hgroupoid H
    let a := p ≫ pullback.fst s t
    let b := p ≫ pullback.snd s t
    have hab : a ≫ s = b ≫ t := by simp [a, b, pullback.condition]
    let f := (φ (b ≫ s) (b ≫ t)).symm ⟨b, rfl, rfl⟩
    let g := (φ (b ≫ t) (a ≫ t)).symm ⟨a, hab, rfl⟩
    have hf : (φ _ _ f).val = b := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hg : (φ _ _ g).val = a := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hfg : (φ _ _ (f ≫ g)).val = p ≫ c := by
      rw [hc]
      congr 1
      apply pullback.hom_ext <;> simp [hf, hg, a, b]
    rw [← hfg]
    exact (φ _ _ (f ≫ g)).property
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (hid U (𝟙 U)).1
  · simpa using (hid U (𝟙 U)).2
  · simpa using (hinv R (𝟙 R)).1
  · simpa using (hinv R (𝟙 R)).2
  · simpa using (hcomp (pullback s t) (𝟙 _)).1
  · simpa using (hcomp (pullback s t) (𝟙 _)).2
  · intro H a p hp₀ hp₁
    obtain ⟨G, φ, he, -, hc⟩ := hgroupoid H
    let f := (φ (a ≫ s) (a ≫ t)).symm ⟨a, rfl, rfl⟩
    have hf : (φ _ _ f).val = a := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hidf := hc _ _ _ f (𝟙 (a ≫ t))
    simp only [Category.comp_id] at hidf
    calc
      p ≫ c = _ := congrArg (fun v ↦ v ≫ c) (show p = _ by
        apply pullback.hom_ext <;> simp [hp₀, hp₁, hf, he])
      _ = _ := hidf.symm
      _ = a := hf
  · intro H a p hp₀ hp₁
    obtain ⟨G, φ, he, -, hc⟩ := hgroupoid H
    let f := (φ (a ≫ s) (a ≫ t)).symm ⟨a, rfl, rfl⟩
    have hf : (φ _ _ f).val = a := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hidf := hc _ _ _ (𝟙 (a ≫ s)) f
    simp only [Category.id_comp] at hidf
    calc
      p ≫ c = _ := congrArg (fun v ↦ v ≫ c) (show p = _ by
        apply pullback.hom_ext <;> simp [hp₀, hp₁, hf, he])
      _ = _ := hidf.symm
      _ = a := hf
  · intro H a p hp₀ hp₁
    obtain ⟨G, φ, he, hi, hc⟩ := hgroupoid H
    let f := (φ (a ≫ s) (a ≫ t)).symm ⟨a, rfl, rfl⟩
    have hf : (φ _ _ f).val = a := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hfi : (φ _ _ (Groupoid.inv f)).val = a ≫ i := by
      simpa only [hf] using hi _ _ f
    have hif := hc _ _ _ f (Groupoid.inv f)
    simp only [Groupoid.comp_inv] at hif
    calc
      p ≫ c = _ := congrArg (fun v ↦ v ≫ c) (show p = _ by
        apply pullback.hom_ext <;>
          simp only [pullback.lift_fst, pullback.lift_snd, hp₀, hp₁, hfi, hf])
      _ = _ := hif.symm
      _ = _ := he _
      _ = a ≫ s ≫ e := Category.assoc _ _ _
  · intro H a p hp₀ hp₁
    obtain ⟨G, φ, he, hi, hc⟩ := hgroupoid H
    let f := (φ (a ≫ s) (a ≫ t)).symm ⟨a, rfl, rfl⟩
    have hf : (φ _ _ f).val = a := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hfi : (φ _ _ (Groupoid.inv f)).val = a ≫ i := by
      simpa only [hf] using hi _ _ f
    have hif := hc _ _ _ (Groupoid.inv f) f
    simp only [Groupoid.inv_comp] at hif
    calc
      p ≫ c = _ := congrArg (fun v ↦ v ≫ c) (show p = _ by
        apply pullback.hom_ext <;>
          simp only [pullback.lift_fst, pullback.lift_snd, hp₀, hp₁, hfi, hf])
      _ = _ := hif.symm
      _ = _ := he _
      _ = a ≫ t ≫ e := Category.assoc _ _ _
  · intro H p q r z hpq hr₀ hr₁ hz₀ hz₁
    obtain ⟨G, φ, -, -, hc⟩ := hgroupoid H
    let a := p ≫ pullback.fst s t
    let b := p ≫ pullback.snd s t
    let d := q ≫ pullback.snd s t
    have hab : a ≫ s = b ≫ t := by simp [a, b, pullback.condition]
    have hbd : b ≫ s = d ≫ t := by
      dsimp [b, d]
      rw [hpq]
      simp [pullback.condition]
    let f := (φ (d ≫ s) (d ≫ t)).symm ⟨d, rfl, rfl⟩
    let g := (φ (d ≫ t) (b ≫ t)).symm ⟨b, hbd, rfl⟩
    let h := (φ (b ≫ t) (a ≫ t)).symm ⟨a, hab, rfl⟩
    have hf : (φ _ _ f).val = d := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hg : (φ _ _ g).val = b := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hh : (φ _ _ h).val = a := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hgh : (φ _ _ (g ≫ h)).val = p ≫ c := by
      rw [hc]
      congr 1
      apply pullback.hom_ext <;> simp [hg, hh, a, b]
    have hfg : (φ _ _ (f ≫ g)).val = q ≫ c := by
      rw [hc]
      congr 1
      apply pullback.hom_ext <;> simp [hf, hg, b, d, hpq]
    have hl : (φ _ _ (f ≫ (g ≫ h))).val = r ≫ c := by
      rw [hc]
      congr 1
      apply pullback.hom_ext <;> simp [hf, hgh, d, hr₀, hr₁]
    have hr : (φ _ _ ((f ≫ g) ≫ h)).val = z ≫ c := by
      rw [hc]
      congr 1
      apply pullback.hom_ext <;> simp [hh, hfg, a, hz₀, hz₁]
    exact hl.symm.trans ((congrArg (fun k ↦ (φ _ _ k).val)
      (Category.assoc f g h).symm).trans hr)

private lemma polyCoord_comp {H K : Scheme.{u}} {A : CommRingCat.{u}}
    (f : H ⟶ K) (g : K ⟶ polySpec A) :
    polyCoord (f ≫ g) = f.appTop (polyCoord g) := by
  simp only [polyCoord, pointRing, Scheme.Hom.comp_appTop]
  rfl

-- Composable polynomial arrows have the same coordinate; compose their base arrows.
private def polyPair {A B : CommRingCat.{u}} (s t : Spec B ⟶ Spec A) :
    pullback (polyMap s) (polyMap t) ⟶ pullback s t :=
  pullback.lift (pullback.fst _ _ ≫ polyBase B) (pullback.snd _ _ ≫ polyBase B) (by
    simp only [Category.assoc, ← polyMap_base]
    simp only [← Category.assoc, pullback.condition])

private def polyComp {A B : CommRingCat.{u}} (s t : Spec B ⟶ Spec A)
    (c : pullback s t ⟶ Spec B) : pullback (polyMap s) (polyMap t) ⟶ polySpec B :=
  polyLift (polyPair s t ≫ c) (polyCoord (pullback.snd (polyMap s) (polyMap t)))

@[reassoc]
private lemma polyComp_base {A B : CommRingCat.{u}} (s t : Spec B ⟶ Spec A)
    (c : pullback s t ⟶ Spec B) :
    polyComp s t c ≫ polyBase B = polyPair s t ≫ c := polyLift_base _ _

private lemma polyComp_coord {H : Scheme.{u}} {A B : CommRingCat.{u}}
    (s t : Spec B ⟶ Spec A) (c : pullback s t ⟶ Spec B)
    (p : H ⟶ pullback (polyMap s) (polyMap t)) :
    polyCoord (p ≫ polyComp s t c) = polyCoord (p ≫ pullback.snd _ _) := by
  rw [polyCoord_comp, polyComp, polyLift_coord, ← polyCoord_comp]

private lemma polyPair_fst {H : Scheme.{u}} {A B : CommRingCat.{u}}
    (s t : Spec B ⟶ Spec A) (p : H ⟶ pullback (polyMap s) (polyMap t)) :
    (p ≫ polyPair s t) ≫ pullback.fst s t = (p ≫ pullback.fst _ _) ≫ polyBase B := by
  simp [polyPair]

private lemma polyPair_snd {H : Scheme.{u}} {A B : CommRingCat.{u}}
    (s t : Spec B ⟶ Spec A) (p : H ⟶ pullback (polyMap s) (polyMap t)) :
    (p ≫ polyPair s t) ≫ pullback.snd s t = (p ≫ pullback.snd _ _) ≫ polyBase B := by
  simp [polyPair]

private lemma polyPair_coords {H : Scheme.{u}} {A B : CommRingCat.{u}}
    (s t : Spec B ⟶ Spec A) (p : H ⟶ pullback (polyMap s) (polyMap t)) :
    polyCoord (p ≫ pullback.fst _ _) = polyCoord (p ≫ pullback.snd _ _) := by
  have hc := congrArg polyCoord (congrArg (fun k ↦ p ≫ k)
    (pullback.condition (f := polyMap s) (g := polyMap t)))
  simpa only [← Category.assoc, polyMap_coord] using hc

-- Verify each law by its base projection and its polynomial coordinate.
private theorem polyGroupoid {A B : CommRingCat.{u}} (s t : Spec B ⟶ Spec A)
    (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    (hG : Scheme.IsGroupoid s t e i c) :
    Scheme.IsGroupoid (polyMap s) (polyMap t) (polyMap e) (polyMap i) (polyComp s t c) := by
  have map_base {C D : CommRingCat.{u}} (f : Spec D ⟶ Spec C)
      {H : Scheme.{u}} (a : H ⟶ polySpec D) :
      (a ≫ polyMap f) ≫ polyBase C = (a ≫ polyBase D) ≫ f := by
    simp only [Category.assoc, polyMap_base]
  have comp_base {H : Scheme.{u}} (p : H ⟶ pullback (polyMap s) (polyMap t)) :
      (p ≫ polyComp s t c) ≫ polyBase B = (p ≫ polyPair s t) ≫ c := by
    simp only [Category.assoc, polyComp_base]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply polyPoint_ext
    · simp only [Category.assoc, polyMap_base_assoc, polyMap_base, Category.id_comp]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ polyBase A ≫ f) hG.source_id).trans (Category.comp_id _))
    · simp only [polyMap_coord, polyMap_selfcoord]
  · apply polyPoint_ext
    · simp only [Category.assoc, polyMap_base_assoc, polyMap_base, Category.id_comp]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ polyBase A ≫ f) hG.target_id).trans (Category.comp_id _))
    · simp only [polyMap_coord, polyMap_selfcoord]
  · apply polyPoint_ext
    · simp only [Category.assoc, polyMap_base_assoc, polyMap_base]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ polyBase B ≫ f) hG.source_inv)
    · simp only [polyMap_coord, polyMap_selfcoord]
  · apply polyPoint_ext
    · simp only [Category.assoc, polyMap_base_assoc, polyMap_base]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ polyBase B ≫ f) hG.target_inv)
    · simp only [polyMap_coord, polyMap_selfcoord]
  · apply polyPoint_ext
    · simp only [Category.assoc, polyMap_base, polyComp_base_assoc]
      rw [hG.source_comp]
      simp [polyPair]
    · simp only [polyMap_coord, polyComp, polyLift_coord]
  · apply polyPoint_ext
    · simp only [Category.assoc, polyMap_base, polyComp_base_assoc]
      rw [hG.target_comp]
      simp [polyPair]
    · simp only [polyMap_coord, polyComp, polyLift_coord]
      simpa only [Category.id_comp] using (polyPair_coords s t (𝟙 _)).symm
  · intro H a p hp₀ hp₁
    apply polyPoint_ext
    · rw [comp_base]
      apply hG.id_comp H (a ≫ polyBase B) (p ≫ polyPair s t)
      · rw [polyPair_fst, hp₀]
        simp only [← Category.assoc, map_base]
      · rw [polyPair_snd, hp₁]
    · rw [polyComp_coord, hp₁]
  · intro H a p hp₀ hp₁
    apply polyPoint_ext
    · rw [comp_base]
      apply hG.comp_id H (a ≫ polyBase B) (p ≫ polyPair s t)
      · rw [polyPair_fst, hp₀]
      · rw [polyPair_snd, hp₁]
        simp only [← Category.assoc, map_base]
    · simp only [polyComp_coord, hp₁, ← Category.assoc, polyMap_coord]
  · intro H a p hp₀ hp₁
    apply polyPoint_ext
    · rw [comp_base]
      simp only [← Category.assoc, map_base]
      simp only [Category.assoc]
      apply hG.inv_comp H (a ≫ polyBase B) (p ≫ polyPair s t)
      · rw [polyPair_fst, hp₀, map_base]
      · rw [polyPair_snd, hp₁]
    · simp only [polyComp_coord, hp₁, ← Category.assoc, polyMap_coord]
  · intro H a p hp₀ hp₁
    apply polyPoint_ext
    · rw [comp_base]
      simp only [← Category.assoc, map_base]
      simp only [Category.assoc]
      apply hG.comp_inv H (a ≫ polyBase B) (p ≫ polyPair s t)
      · rw [polyPair_fst, hp₀]
      · rw [polyPair_snd, hp₁, map_base]
    · simp only [polyComp_coord, hp₁, ← Category.assoc, polyMap_coord]
  · intro H p q r z hpq hr₀ hr₁ hz₀ hz₁
    apply polyPoint_ext
    · rw [comp_base, comp_base]
      apply hG.assoc H (p ≫ polyPair s t) (q ≫ polyPair s t)
        (r ≫ polyPair s t) (z ≫ polyPair s t)
      · rw [polyPair_snd, polyPair_fst, hpq]
      · rw [polyPair_fst, hr₀, comp_base]
      · rw [polyPair_snd, polyPair_snd, hr₁]
      · rw [polyPair_fst, polyPair_fst, hz₀]
      · rw [polyPair_snd, hz₁, comp_base]
    · rw [polyComp_coord, polyComp_coord, hr₁, hz₁, polyComp_coord]

/-- The source norm of the target image of a polynomial has invariant coefficients.
The hypothesis `hgroupoid` says precisely that the indicated scheme maps define a
functorial groupoid on test points: its hom sets are identified with the arrows having
the specified source and target, and identity, inverse and composition are the given
scheme maps. Naturality follows because all these operations are induced by scheme maps.
The variable `Q` is the norm section, specified by its finite free affine chart formula
`hQ`. This characterizes the glued norm uniquely, rather than using `Algebra.norm` on
a possibly nonfree global module. Existence is supplied by the norm-charts dependency
applied to the polynomial-coordinate source morphism. Thus quantifying over `Q` and
its chart formula asserts invariance of the specified norm, with no choice of a norm map.

Source: Stacks Project, Tag 03BH and `lemma-integral-over-invariants`, second paragraph;
Tag 02DV(1),(3) (blueprint: lem-a1-affine-groupoid-polynomial-norm-invariant).

Proof plan:
1. Adjoin one common polynomial coordinate to the affine object and arrow schemes.
   All groupoid operations extend with that coordinate fixed. Finite local freeness
   survives base change, and the rank may vary on the original local charts.
2. Apply `lem-a1-affine-groupoid-invariant-norm` to this groupoid and to `F`.
   Its norm is the glued local determinant specified by `hQ`, by uniqueness of gluing.
   Hence the source and target images of `Q` are equal.
3. The two polynomial maps act coefficientwise. Their equality says exactly that
   every coefficient of `Q` lies in the equalizer of the original source and target
   ring maps, namely that `Q` belongs to `C[T]`.
-/
theorem affine_groupoid_polynomial_norm_invariant
    (A B : CommRingCat.{u}) (s t : Spec B ⟶ Spec A)
    (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]
    (hgroupoid : ∀ H : Scheme.{u},
      ∃ (G : Groupoid.{u} (H ⟶ Spec A))
        (φ : ∀ x y : H ⟶ Spec A,
          @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y ≃
            {r : H ⟶ Spec B // r ≫ s = x ∧ r ≫ t = y}),
        (∀ x : H ⟶ Spec A,
          (φ x x (@CategoryStruct.id _ G.toCategory.toCategoryStruct x)).val = x ≫ e) ∧
        (∀ (x y : H ⟶ Spec A)
          (f : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y),
          (φ y x (@Groupoid.inv _ G x y f)).val = (φ x y f).val ≫ i) ∧
        (∀ (x y z : H ⟶ Spec A)
          (f : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y)
          (g : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver y z),
          (φ x z (@CategoryStruct.comp _ G.toCategory.toCategoryStruct x y z f g)).val =
            pullback.lift (φ y z g).val (φ x y f).val
              ((φ y z g).property.1.trans (φ x y f).property.2.symm) ≫ c))
    (F Q : Polynomial A)
    (hQ : ∀ x : Spec (CommRingCat.of (Polynomial A)),
      ∃ V : (Spec (CommRingCat.of (Polynomial A))).Opens,
        x ∈ V ∧ IsAffineOpen V ∧
        @Module.Free Γ(Spec (CommRingCat.of (Polynomial A)), V)
          Γ(Spec (CommRingCat.of (Polynomial B)),
            Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Spec.homEquiv s).hom)) ⁻¹ᵁ V)
          _ _ ((Spec.map (CommRingCat.ofHom
            (Polynomial.mapRingHom (Spec.homEquiv s).hom))).app V).hom.toAlgebra.toModule ∧
        @Module.Finite Γ(Spec (CommRingCat.of (Polynomial A)), V)
          Γ(Spec (CommRingCat.of (Polynomial B)),
            Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Spec.homEquiv s).hom)) ⁻¹ᵁ V)
          _ _ ((Spec.map (CommRingCat.ofHom
            (Polynomial.mapRingHom (Spec.homEquiv s).hom))).app V).hom.toAlgebra.toModule ∧
        (Spec (CommRingCat.of (Polynomial A))).presheaf.map
            (homOfLE (le_top : V ≤ ⊤)).op
            ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).inv Q) =
          @Algebra.norm Γ(Spec (CommRingCat.of (Polynomial A)), V)
            Γ(Spec (CommRingCat.of (Polynomial B)),
              Spec.map (CommRingCat.ofHom
                (Polynomial.mapRingHom (Spec.homEquiv s).hom)) ⁻¹ᵁ V)
            _ _ ((Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (Spec.homEquiv s).hom))).app V).hom.toAlgebra
            ((Spec (CommRingCat.of (Polynomial B))).presheaf.map
              (homOfLE le_top).op
              ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial B))).inv
                (Polynomial.map (Spec.homEquiv t).hom F)))) :
    Polynomial.map (Spec.homEquiv s).hom Q = Polynomial.map (Spec.homEquiv t).hom Q := by
  dsimp only [Spec.homEquiv, Equiv.coe_fn_mk] at hQ
  have hs : Spec.homEquiv s = Spec.preimage s := rfl
  have ht : Spec.homEquiv t = Spec.preimage t := rfl
  have hG := groupoidLaws_of_points s t e i c hgroupoid
  have : (polyMap s).IsFiniteLocallyFree := polyMap_finiteLocallyFree s
  have : (polyMap t).IsFiniteLocallyFree := polyMap_finiteLocallyFree t
  have h := affineGroupoid_invariant_norm
    (CommRingCat.of (Polynomial A)) (CommRingCat.of (Polynomial B))
    (polyMap s) (polyMap t) (polyMap e) (polyMap i) (polyComp s t c)
    (polyGroupoid s t e i c hG) F Q (by
      simpa only [polyMap, Spec.preimage_map, CommRingCat.hom_ofHom,
        Polynomial.coe_mapRingHom] using hQ)
  change (Spec.preimage (polyMap s)).hom Q = (Spec.preimage (polyMap t)).hom Q at h
  simpa only [polyMap, Spec.preimage_map, CommRingCat.hom_ofHom,
    Polynomial.coe_mapRingHom, hs, ht] using h

end

end AlgebraicGeometry
