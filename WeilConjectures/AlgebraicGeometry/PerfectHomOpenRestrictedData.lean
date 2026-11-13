/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictionMap
public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedEquiv
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedMaps
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedQCoh

/-! # Compatible open restriction of representing Hom data

The compatibility at identity morphisms determines compatibility at every testing morphism.

## References

* Stacks Project, Tags 079W, 08FE and 09RE.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section

private theorem restriction_map_natural
    {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {M N Q : schemeDerivedCategory Y} (g : M ⟶ N)
    (f : (derivedPullback (pullback.fst s r)).obj N ⟶
      (derivedPullback (pullback.fst s r)).obj Q) :
    perfectHomOpenRestrictionMap s B r a
        ((derivedPullback (pullback.fst s r)).map g ≫ f) =
      (derivedPullback (pullback.fst (B.ι ≫ s) r)).map
          ((schemeMVDerivedRestriction Y B).map g) ≫
        perfectHomOpenRestrictionMap s B r a f := by
  unfold perfectHomOpenRestrictionMap
  rw [Functor.map_comp]
  have hn := (perfectHomOpenPullbackComparison s B r a).inv.naturality g
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]

/-- Compatibility at a stage identity implies compatibility at every testing morphism. -/
theorem perfect_hom_open_restricted_stage_pinned
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d)
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d)
    (he : ∀ j : Set.Ici i,
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj (F.obj j)) (𝟙 _) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j (F.obj j) (𝟙 _))) :
    ∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f) := by
  intro j M f
  have hb := e.stageNatural j _ _ ((schemeMVDerivedRestriction Y B).map f) (𝟙 _)
  have hh := h.stageNatural j M (F.obj j) f (𝟙 _)
  simp only [Category.comp_id] at hb hh
  rw [hb, he j, hh, restriction_map_natural]

/-- Compatibility at the apex identity implies compatibility at every testing morphism. -/
theorem perfect_hom_open_restricted_limit_pinned
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d)
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d)
    (he : e.limitEquiv ((schemeMVDerivedRestriction Y B).obj d.pt) (𝟙 _) =
      perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
        (h.limitEquiv d.pt (𝟙 _))) :
    ∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
      e.limitEquiv ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (h.limitEquiv M f) := by
  intro M f
  have hb := e.limitNatural _ _ ((schemeMVDerivedRestriction Y B).map f) (𝟙 _)
  have hh := h.limitNatural M d.pt f (𝟙 _)
  simp only [Category.comp_id] at hb hh
  rw [hb, he, hh, restriction_map_natural]

/-- Combine the identity-normalized stage and apex equations. -/
theorem perfect_hom_open_restricted_data_pinned
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d)
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d)
    (hs : ∀ j : Set.Ici i,
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj (F.obj j)) (𝟙 _) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j (F.obj j) (𝟙 _)))
    (hl : e.limitEquiv ((schemeMVDerivedRestriction Y B).obj d.pt) (𝟙 _) =
      perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
        (h.limitEquiv d.pt (𝟙 _))) :
    (∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f)) ∧
    (∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
      e.limitEquiv ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (h.limitEquiv M f)) := by
  exact ⟨perfect_hom_open_restricted_stage_pinned R c s B a Q F d h e hs,
    perfect_hom_open_restricted_limit_pinned R c s B a Q F d h e hl⟩

/-- Exact open restriction carries a representing pullback Hom cocone to a representing
cocone for the restricted base scheme. The two additional equations tie its Hom equivalences
on restricted testing objects to the concrete `perfectHomOpenRestrictionMap`
(Stacks, Tags 079W, 08FE and 09RE). -/
theorem perfect_hom_open_restricted_data
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens)
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    let L := schemeMVDerivedRestriction Y B
    ∃ hB : PerfectHomPushPullData R c (B.ι ≫ s) (L.obj Q) (F ⋙ L) (L.mapCocone d),
      (∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
        hB.stageEquiv j (L.obj M) (L.map f) =
          perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a
            (h.stageEquiv j M f)) ∧
      (∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
        hB.limitEquiv (L.obj M) (L.map f) =
          perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv M f)) := by
  obtain ⟨e, hs, hl⟩ := perfect_hom_open_restricted_pinned_equiv R c s B a Q F d h
  obtain ⟨hs', hl'⟩ := perfect_hom_open_restricted_data_pinned R c s B a Q F d h e hs hl
  obtain ⟨hm, hc⟩ := perfect_hom_open_restricted_pinned_maps R c s B a Q F d h e hs' hl'
  obtain ⟨hq, hq'⟩ := perfect_hom_open_restricted_qcoh R c s B Q F d h
  exact ⟨{
    stageQCoh := hq
    limitQCoh := hq'
    stageEquiv := e.stageEquiv
    limitEquiv := e.limitEquiv
    stageNatural := e.stageNatural
    limitNatural := e.limitNatural
    stageMap := hm
    limitMap := hc }, hs', hl'⟩

end
end AlgebraicGeometry
