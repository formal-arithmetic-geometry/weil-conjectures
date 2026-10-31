/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential

/-! # Centred etale coordinate-difference neighbourhoods

Source: chart proof, Step 1.
(blueprint: lem-pur-chart-coordinate-difference-neighbourhood).

This extracts the existing proved geometry with its declaration names and data unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The actual coordinate differences y_i-x_i, based at the first projection.
Source: chart proof, Steps 1--2
(blueprint: lem-pur-chart-coordinate-difference-neighbourhood). -/
def chartCoordinateDifferences {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) :
    pullback h h ⟶ AffineSpace (ULift.{u} (Fin d)) U :=
  AffineSpace.homOfVector (pullback.fst h h) fun i ↦
    (pullback.snd h h ≫ u).appTop (AffineSpace.coord V i) -
      (pullback.fst h h ≫ u).appTop (AffineSpace.coord V i)

private theorem pullback_of_cone_equations
    {C : Type*} [Category C] {U O A Q T : C}
    (s : U ⟶ O) (u : U ⟶ A) (v : O ⟶ Q) (e : A ⟶ Q)
    (g : O ⟶ T) (z : U ⟶ T) (r : O ⟶ U)
    (H : IsPullback s u v e) (hs : s ≫ g = (𝟙 U) ≫ z)
    (hr : s ≫ r = 𝟙 U)
    (hb : ∀ c : PullbackCone g z, c.fst ≫ r = c.snd)
    (heq : ∀ c : PullbackCone g z, c.fst ≫ v = (c.snd ≫ u) ≫ e) :
    IsPullback s (𝟙 U) g z := by
  let l (c : PullbackCone g z) := H.lift c.fst (c.snd ≫ u) (heq c)
  refine ⟨⟨hs⟩, ⟨PullbackCone.IsLimit.mk _ l ?_ ?_ ?_⟩⟩
  · intro c
    exact H.lift_fst _ _ (heq c)
  · intro c
    calc
      l c ≫ 𝟙 U = (l c ≫ s) ≫ r := by rw [Category.assoc, hr]
      _ = c.fst ≫ r := congrArg (fun q ↦ q ≫ r) (H.lift_fst _ _ (heq c))
      _ = c.snd := hb c
  · intro c m hm₁ hm₂
    apply H.hom_ext
    · exact hm₁.trans (H.lift_fst _ _ (heq c)).symm
    · exact (congrArg (fun q ↦ q ≫ u) ((Category.comp_id m).symm.trans hm₂)).trans
        (H.lift_snd _ _ (heq c)).symm

private theorem chartCoordinateDifferences_etale {U V : Scheme.{u}}
    (d : ℕ) (h : U ⟶ V) (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale u] (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    Etale (chartCoordinateDifferences d h u) := by
  classical
  subst h
  let I := ULift.{u} (Fin d)
  let p : AffineSpace I V ⟶ V := AffineSpace I V ↘ V
  let raw := AffineSpace.homOfVector (pullback.fst (u ≫ p) (u ≫ p))
    (fun i ↦ (pullback.snd (u ≫ p) (u ≫ p) ≫ u).appTop (AffineSpace.coord V i))
  have hcomm : raw ≫ AffineSpace.map I (u ≫ p) =
      pullback.snd (u ≫ p) (u ≫ p) ≫ u := by
    dsimp only [raw, I]
    rw [AffineSpace.homOfVector_comp_map]
    apply AffineSpace.hom_ext
    · rw [AffineSpace.homOfVector_over]
      exact pullback.condition (f := u ≫ p) (g := u ≫ p)
    · intro i
      rw [AffineSpace.homOfVector_appTop_coord]
  have hp : IsPullback raw (pullback.snd (u ≫ p) (u ≫ p))
      (AffineSpace.map I (u ≫ p)) u := by
    have hout : IsPullback (raw ≫ (AffineSpace I U ↘ U))
        (pullback.snd (u ≫ p) (u ≫ p)) (u ≫ p) (u ≫ p) := by
      simpa only [raw, I, AffineSpace.homOfVector_over] using
        IsPullback.of_hasPullback (u ≫ p) (u ≫ p)
    exact hout.of_right hcomm (AffineSpace.isPullback_map (n := I) (u ≫ p)).flip
  let : Etale raw := MorphismProperty.of_isPullback hp.flip inferInstance
  let a : I → Γ(U, ⊤) := fun i ↦ -u.appTop (AffineSpace.coord V i)
  let τ : AffineSpace I U ≅ AffineSpace I U :=
    ⟨AffineSpace.translation a, AffineSpace.translation (-a), by
      rw [← AffineSpace.translation_add, add_neg_cancel, AffineSpace.translation_zero], by
      rw [← AffineSpace.translation_add, neg_add_cancel, AffineSpace.translation_zero]⟩
  have ht : raw ≫ τ.hom = chartCoordinateDifferences d (u ≫ p) u := by
    apply AffineSpace.hom_ext
    · change raw ≫ AffineSpace.translation a ≫ (AffineSpace I U ↘ U) =
        chartCoordinateDifferences d (u ≫ p) u ≫ (AffineSpace I U ↘ U)
      dsimp only [I]
      simp only [AffineSpace.translation_over, raw, chartCoordinateDifferences,
        AffineSpace.homOfVector_over]
    · intro i
      change raw.appTop ((AffineSpace.translation a).appTop (AffineSpace.coord U i)) = _
      rw [AffineSpace.translation_appTop_coord, map_add]
      dsimp only [raw]
      rw [AffineSpace.homOfVector_appTop_coord]
      change (pullback.snd (u ≫ p) (u ≫ p) ≫ u).appTop (AffineSpace.coord V i) +
        (raw ≫ (AffineSpace I U ↘ U)).appTop (a i) = _
      change (pullback.snd (u ≫ p) (u ≫ p) ≫ u).appTop (AffineSpace.coord V i) +
        (AffineSpace.homOfVector (pullback.fst (u ≫ p) (u ≫ p))
          (fun j ↦ (pullback.snd (u ≫ p) (u ≫ p) ≫ u).appTop
            (AffineSpace.coord V j)) ≫ (AffineSpace I U ↘ U)).appTop (a i) = _
      dsimp only [I]
      rw [AffineSpace.homOfVector_over]
      simp only [a, map_neg, chartCoordinateDifferences,
        AffineSpace.homOfVector_appTop_coord, sub_eq_add_neg]
      rfl
  let : IsIso τ.hom := τ.isIso_hom
  exact ht ▸ Etale.etale_comp raw τ.hom

/-- Differences give a Cartesian centred etale neighbourhood of the entire diagonal.
The zero fibre is exactly the diagonal after discarding its other etale components.
Source: chart proof, Step 1 (blueprint: lem-pur-chart-coordinate-difference-neighbourhood).

Proof: the product of the coordinate etale map with itself is etale. The inverse
image of the affine diagonal is U times_A U; its own diagonal U is open and
closed because u is separated etale. Remove its complementary closed component.
On the resulting open, subtraction makes the displayed zero square Cartesian.
The shear (x,y) -> (x,y-x) is an affine-space automorphism; base change of u and
this shear show that the displayed difference map is etale there. At d=0 the
same argument gives the identity pair, and it also applies to empty U. -/
theorem chartCoordinateDifferences_neighbourhood {U V : Scheme.{u}}
    (d : ℕ) (h : U ⟶ V) (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale u] [IsSeparated u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃ (O : (pullback h h).Opens) (s : U ⟶ O.toScheme),
      s ≫ O.ι = pullback.diagonal h ∧
      Etale (O.ι ≫ chartCoordinateDifferences d h u) ∧
      IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) U) := by
  classical
  subst h
  let I := ULift.{u} (Fin d)
  let p : AffineSpace I V ⟶ V := AffineSpace I V ↘ V
  let : Etale (chartCoordinateDifferences d (u ≫ p) u) :=
    chartCoordinateDifferences_etale d _ u rfl
  obtain ⟨O, s, _, hs, H, _, _⟩ := ChartNormalDifferential.chartGeometry p u
  refine ⟨O, s, hs, inferInstance, ?_⟩
  have hsp : s ≫ O.ι ≫ pullback.fst (u ≫ p) (u ≫ p) = 𝟙 U := by
    rw [← Category.assoc, hs, pullback.diagonal_fst]
  have hsz : s ≫ (O.ι ≫ chartCoordinateDifferences d (u ≫ p) u) =
      (𝟙 U) ≫ AffineSpace.zeroSection I U := by
    apply AffineSpace.hom_ext
    · change (s ≫ O.ι ≫ chartCoordinateDifferences d (u ≫ p) u) ≫
        (AffineSpace I U ↘ U) = ((𝟙 U) ≫ AffineSpace.zeroSection I U) ≫
          (AffineSpace I U ↘ U)
      dsimp only [I]
      simp only [Category.assoc, chartCoordinateDifferences,
        AffineSpace.homOfVector_over, hsp, AffineSpace.zeroSection_over,
        Category.id_comp]
    · intro i
      dsimp only [I]
      simp only [← Category.assoc, hs, chartCoordinateDifferences,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, map_sub]
      simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, pullback.diagonal_snd, pullback.diagonal_fst,
        Category.id_comp, sub_self, AffineSpace.zeroSection_appTop_coord, map_zero]
  have hb (c : PullbackCone (O.ι ≫ chartCoordinateDifferences d (u ≫ p) u)
    (AffineSpace.zeroSection I U)) : c.fst ≫ O.ι ≫ pullback.fst (u ≫ p) (u ≫ p) = c.snd := by
    have hh := congrArg (fun f ↦ f ≫ (AffineSpace I U ↘ U)) c.condition
    change (c.fst ≫ O.ι ≫ chartCoordinateDifferences d (u ≫ p) u) ≫
      (AffineSpace I U ↘ U) = (c.snd ≫ AffineSpace.zeroSection I U) ≫ _ at hh
    dsimp only [I] at hh
    simpa only [Category.assoc, chartCoordinateDifferences,
      AffineSpace.homOfVector_over, AffineSpace.zeroSection_over,
      Category.comp_id] using hh
  have heq (c : PullbackCone (O.ι ≫ chartCoordinateDifferences d (u ≫ p) u)
    (AffineSpace.zeroSection I U)) : c.fst ≫ (O.ι ≫ pullback.map (u ≫ p) (u ≫ p) p p
      u u (𝟙 V) (by simp) (by simp)) = (c.snd ≫ u) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id] using congrArg (fun f ↦ f ≫ u) (hb c)
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id]
      apply AffineSpace.hom_ext
      · change c.fst ≫ O.ι ≫ pullback.snd (u ≫ p) (u ≫ p) ≫ u ≫ p =
          c.snd ≫ u ≫ p
        rw [← pullback.condition]
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ u ≫ p) (hb c)
      · intro i
        have hh := congrArg (fun f ↦ f.appTop (AffineSpace.coord U i)) c.condition
        change (c.fst ≫ O.ι ≫ chartCoordinateDifferences d (u ≫ p) u).appTop
          (AffineSpace.coord U i) = (c.snd ≫ AffineSpace.zeroSection I U).appTop
            (AffineSpace.coord U i) at hh
        dsimp only [I] at hh
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          chartCoordinateDifferences, AffineSpace.homOfVector_appTop_coord,
          map_sub, AffineSpace.zeroSection_appTop_coord, map_zero] at hh
        have hh' := sub_eq_zero.mp hh
        have hb' := congrArg (fun f ↦ f.appTop (u.appTop (AffineSpace.coord V i))) (hb c)
        change c.fst.appTop (O.ι.appTop
          ((pullback.fst (u ≫ p) (u ≫ p)).appTop
            (u.appTop (AffineSpace.coord V i)))) =
          c.snd.appTop (u.appTop (AffineSpace.coord V i)) at hb'
        exact hh'.trans hb'
  exact pullback_of_cone_equations s u _ _ _ _
    (O.ι ≫ pullback.fst (u ≫ p) (u ≫ p)) H hsz hsp hb heq

end WeilConjectures.PurityFiniteSetting
