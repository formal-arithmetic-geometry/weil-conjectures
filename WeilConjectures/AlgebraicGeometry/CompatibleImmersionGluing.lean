/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Gluing

/-! # Descent of compatible immersions

Source: Stacks Project, Tags 01JB and 01JC; Tag 0BDL, gluing characterized patches.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A compatible local immersion has the expected open overlap with every other patch.
Source: Stacks Project, Tag 0BDL, final paragraph, characterized local patches. -/
private theorem compatibleImmersion_openOverlap (S : Scheme.{u})
    (U : S → S.Opens) (W : S → Scheme.{u})
    (j : ∀ s : S, W s ⟶ (U s).toScheme) (hj : ∀ s : S, IsImmersion (j s))
    (hcompat : ∀ (i k : S) {T : Scheme.{u}}
      (a : T ⟶ (U i).toScheme) (b : T ⟶ (U k).toScheme),
      a ≫ (U i).ι = b ≫ (U k).ι →
      ((∃ h : T ⟶ W i, h ≫ j i = a) ↔ (∃ h : T ⟶ W k, h ≫ j k = b))) :
    ∀ i k : S,
      IsOpenImmersion (Limits.pullback.fst (j i ≫ (U i).ι) (j k ≫ (U k).ι)) ∧
      Set.range (Limits.pullback.fst (j i ≫ (U i).ι) (j k ≫ (U k).ι)) =
        (j i ≫ (U i).ι) ⁻¹' (U k : Set S) := by
  classical
  have (i : S) : IsImmersion (j i) := hj i
  let f : ∀ i : S, W i ⟶ S := fun i ↦ j i ≫ (U i).ι
  have (i : S) : Mono (f i) := by dsimp [f]; infer_instance
  intro i k
  let V := f i ⁻¹ᵁ U k
  obtain ⟨b, hb⟩ := (hcompat i k (V.ι ≫ j i) (f i ∣_ U k)
    (by rw [morphismRestrict_ι]; exact Category.assoc _ _ _)).mp
      ⟨V.ι, rfl⟩
  have hbf : b ≫ f k = V.ι ≫ f i := by
    simp only [f, ← Category.assoc, hb]
    exact morphismRestrict_ι _ _
  have hp : IsPullback V.ι b (f i) (f k) := by
    refine ⟨⟨hbf.symm⟩, ⟨Limits.PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
    · intro s
      apply IsOpenImmersion.lift V.ι s.fst
      rintro x ⟨y, rfl⟩
      rw [Opens.range_ι]
      change f i (s.fst y) ∈ U k
      rw [← Scheme.Hom.comp_apply, s.condition, Scheme.Hom.comp_apply]
      exact (j k (s.snd y)).property
    · intro s
      exact IsOpenImmersion.lift_fac _ _ _
    · intro s
      apply (cancel_mono (f k)).mp
      rw [Category.assoc, hbf, IsOpenImmersion.lift_fac_assoc, s.condition]
    · intro s m h1 _h2
      apply (cancel_mono V.ι).mp
      rw [h1, IsOpenImmersion.lift_fac]
  have hfst : Limits.pullback.fst (f i) (f k) = hp.isoPullback.inv ≫ V.ι :=
    hp.isoPullback_inv_fst.symm
  constructor
  · rw [hfst]
    infer_instance
  · change Set.range (Limits.pullback.fst (f i) (f k)) = (V : Set (W i))
    rw [hfst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hp.isoPullback.inv.surjective, Set.image_univ, Opens.range_ι]

/-- Monomorphisms with open Limits.pullback projections admit a glued open atlas over the base.
Source: Stacks Project, Tags 01JB and 01JC, gluing schemes along open subschemes. -/
private theorem exists_gluedMonoOpenAtlas {I : Type u} (S : Scheme.{u}) (W : I → Scheme.{u})
    (f : ∀ i, W i ⟶ S) (hf : ∀ i, Mono (f i))
    (hopen : ∀ i k, IsOpenImmersion (Limits.pullback.fst (f i) (f k))) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ S) (e : ∀ i, W i ⟶ Z),
      (∀ i, IsOpenImmersion (e i)) ∧
      (∀ z : Z, ∃ i, ∃ x : W i, e i x = z) ∧
      (∀ i, e i ≫ q = f i) ∧
      (∀ i k, Limits.pullback.fst (f i) (f k) ≫ e i =
        Limits.pullback.snd (f i) (f k) ≫ e k) := by
  classical
  have (i : I) : Mono (f i) := hf i
  have (i k : I) : IsOpenImmersion (Limits.pullback.fst (f i) (f k)) := hopen i k
  let t' : ∀ i j k : I,
      Limits.pullback (Limits.pullback.fst (f i) (f j)) (Limits.pullback.fst (f i) (f k)) ⟶
        Limits.pullback (Limits.pullback.fst (f j) (f k)) (Limits.pullback.fst (f j) (f i)) :=
    fun i j k ↦
    Limits.pullback.lift
      (Limits.pullback.lift
        (Limits.pullback.fst (Limits.pullback.fst (f i) (f j)) (Limits.pullback.fst (f i) (f k)) ≫
          Limits.pullback.snd (f i) (f j))
        (Limits.pullback.snd (Limits.pullback.fst (f i) (f j)) (Limits.pullback.fst (f i) (f k)) ≫
          Limits.pullback.snd (f i) (f k))
        (by
          rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
            Limits.pullback.condition, Category.assoc, Limits.pullback.condition, Category.assoc]))
      (Limits.pullback.fst (Limits.pullback.fst (f i) (f j)) (Limits.pullback.fst (f i) (f k)) ≫
        (Limits.pullbackSymmetry (f i) (f j)).hom)
      (by simp)
  have ht' (i j k : I) :
      t' i j k ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.fst (f j) (f k) ≫ f j =
        Limits.pullback.fst (Limits.pullback.fst (f i) (f j)) (Limits.pullback.fst (f i) (f k)) ≫
          Limits.pullback.fst (f i) (f j) ≫ f i := by
    dsimp [t']
    simp only [Limits.pullback.lift_fst_assoc, Category.assoc, ← Limits.pullback.condition]
  let D : Scheme.GlueData.{u} :=
    { J := I
      U := W
      V := fun ij ↦ Limits.pullback (f ij.1) (f ij.2)
      f := fun i j ↦ Limits.pullback.fst (f i) (f j)
      f_id := fun i ↦ inferInstance
      t := fun i j ↦ (Limits.pullbackSymmetry (f i) (f j)).hom
      t_id := fun i ↦ by
        apply (cancel_mono (Limits.pullback.fst (f i) (f i))).mp
        simp only [Limits.pullbackSymmetry_hom_comp_fst, Category.id_comp]
        exact (cancel_mono (f i)).mp (Limits.pullback.condition (f := f i) (g := f i)).symm
      t' := t'
      t_fac := fun i j k ↦ by dsimp [t']; simp
      cocycle := fun i j k ↦ by
        apply (cancel_mono (Limits.pullback.fst _ _ ≫ Limits.pullback.fst (f i) (f j) ≫ f i)).mp
        simp only [Category.id_comp, Category.assoc]
        rw [ht', ht', ht']
      f_open := fun i j ↦ hopen i j }
  let : Limits.HasMulticoequalizer D.toGlueData.diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram D
  let q : D.glued ⟶ S :=
    Limits.Multicoequalizer.desc D.toGlueData.diagram S f (fun ij ↦ by
      change Limits.pullback.fst (f ij.1) (f ij.2) ≫ f ij.1 =
        ((Limits.pullbackSymmetry (f ij.1) (f ij.2)).hom ≫
          Limits.pullback.fst (f ij.2) (f ij.1)) ≫ f ij.2
      rw [Limits.pullbackSymmetry_hom_comp_fst]
      exact Limits.pullback.condition)
  refine ⟨D.glued, q, D.ι, fun i ↦ D.ι_isOpenImmersion i,
    D.ι_jointly_surjective, ?_, ?_⟩
  · intro i
    exact Limits.Multicoequalizer.π_desc D.toGlueData.diagram S f _ i
  · intro i k
    simpa only [D, Category.assoc, Limits.pullbackSymmetry_hom_comp_fst_assoc] using
      (D.glue_condition i k).symm

/-- Compatible immersions over a point-indexed family of opens descend to Cartesian charts.
Source: Stacks Project, Tags 01JB and 01JC, applied to the characterized patches
in the final paragraph of Tag 0BDL. -/
theorem exists_gluedCompatibleImmersionCharts (S : Scheme.{u})
    (U : S → S.Opens)
    (W : S → Scheme.{u}) (j : ∀ s : S, W s ⟶ (U s).toScheme)
    (hj : ∀ s : S, IsImmersion (j s))
    (hcompat : ∀ (i k : S) {T : Scheme.{u}}
      (a : T ⟶ (U i).toScheme) (b : T ⟶ (U k).toScheme),
      a ≫ (U i).ι = b ≫ (U k).ι →
      ((∃ h : T ⟶ W i, h ≫ j i = a) ↔ (∃ h : T ⟶ W k, h ≫ j k = b))) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ S),
      ∀ i : S, ∃ e : W i ⟶ Z, IsPullback (j i) e (U i).ι q := by
  classical
  let f : ∀ i : S, W i ⟶ S := fun i ↦ j i ≫ (U i).ι
  have (i : S) : IsImmersion (j i) := hj i
  have (i : S) : Mono (f i) := by dsimp [f]; infer_instance
  have hov := compatibleImmersion_openOverlap S U W j hj hcompat
  obtain ⟨Z, q, e, he, hcover, hq, hover⟩ :=
    exists_gluedMonoOpenAtlas S W f (fun i ↦ inferInstance) (fun i k ↦ (hov i k).1)
  have (i : S) : IsOpenImmersion (e i) := he i
  have hsat (i : S) : q ⁻¹' (U i : Set S) ⊆ Set.range (e i) := by
    intro z hz
    obtain ⟨k, x, rfl⟩ := hcover z
    have hx : f k x ∈ U i := by
      change q (e k x) ∈ U i at hz
      simpa only [← Scheme.Hom.comp_apply, hq] using hz
    have hr : x ∈ Set.range (Limits.pullback.fst (f k) (f i)) := by
      rw [(hov k i).2]
      exact hx
    obtain ⟨v, hv⟩ := hr
    refine ⟨Limits.pullback.snd (f k) (f i) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hover, Scheme.Hom.comp_apply, hv]
  refine ⟨Z, q, fun i ↦ ⟨e i, ?_⟩⟩
  refine ⟨⟨(hq i).symm⟩, ⟨Limits.PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    apply IsOpenImmersion.lift (e i) s.snd
    rintro z ⟨t, rfl⟩
    apply hsat i
    change q (s.snd t) ∈ U i
    rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
    exact (s.fst t).property
  · intro s
    have hqi : e i ≫ q = j i ≫ (U i).ι := hq i
    rw [← cancel_mono (U i).ι, Category.assoc, ← hqi,
      IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s m _h1 h2
    apply (cancel_mono (e i)).mp
    rw [h2, IsOpenImmersion.lift_fac]

end AlgebraicGeometry.Scheme
