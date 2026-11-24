/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import WeilConjectures.AlgebraicGeometry.PerfectHomLocalComparison
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenStagePresentation

/-! # Recognition of a single-open Hom colimit comparison

## References

* Stacks Project, Tags 09RE and 08BW.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The canonical group-colimit comparison for Hom into a restricted direct image
has a pinned local Hom presentation (Stacks, Tags 09RE and 08BW). -/
theorem perfect_hom_open_colimit_local_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (W : X.Opens) (hW : IsCompact (W : Set X))
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : W ≤ t.opensRange)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ B : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over B))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    let H := schemeMVDerivedRestriction Y (t ⁻¹ᵁ W) ⋙
      schemeDerivedDirectImage (t ⁻¹ᵁ W).ι
    let T := (preadditiveCoyoneda.obj (Opposite.op P)).shift (0 : ℤ) ⋙
      AddCommGrpCat.uliftFunctor.{u}
    PerfectHomLocalComparison R c i X s₀ W
      (colimit.desc (F ⋙ H ⋙ T) ((H ⋙ T).mapCocone d)) := by
  dsimp
  let H := schemeMVDerivedRestriction Y (t ⁻¹ᵁ W) ⋙
    schemeDerivedDirectImage (t ⁻¹ᵁ W).ι
  let T := (preadditiveCoyoneda.obj (Opposite.op P)).shift (0 : ℤ) ⋙
    AddCommGrpCat.uliftFunctor.{u}
  let K := F ⋙ H ⋙ T
  let dK := (H ⋙ T).mapCocone d
  obtain ⟨Z, k, hkI, hk, s', hs', hsL, hsC, hsQ, hD, P', Q', hP', hQ',
    e, b, he, hb⟩ := perfect_hom_open_stage_presentation R c i X s₀ W hW
      Y t ht s hs P Q hP hQ F d h (0 : ℤ)
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j l ↦ by
    obtain ⟨a, hja, hla⟩ := exists_ge_ge j.val l.val
    exact ⟨⟨a, j.property.trans hja⟩, hja, hla⟩⟩
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have : CategoryTheory.IsFiltered (Set.Ici i) := inferInstance
  let G := forget AddCommGrpCat.{max u w}
  have : PreservesFilteredColimitsOfSize.{max u w, max u w} G := inferInstance
  have : PreservesFilteredColimitsOfSize.{u, u} G :=
    preservesFilteredColimitsOfSize_shrink G
  have : PreservesColimit K G := inferInstance
  let D := G.mapCocone (colimit.cocone K)
  refine ⟨Z, k, hkI, hk, s', hs', hsL, hsC, hsQ, hD, P', Q', hP', hQ',
    K ⋙ G, D, isColimitOfPreserves G (colimit.isColimit K),
    (fun j ↦ Equiv.ulift.trans (e j)), ?_, Equiv.refl _,
    Equiv.ulift.trans b, ?_⟩
  · intro j l hjl f
    change e l (f.down ≫ (H.map (F.map (homOfLE hjl)))⟦(0 : ℤ)⟧') = _
    exact he j l hjl f.down
  · intro j f
    change (Equiv.ulift.trans b) ((colimit.desc K dK) ((colimit.ι K j) f)) = _
    rw [← ConcreteCategory.comp_apply, colimit.ι_desc]
    change b (f.down ≫ (H.map (d.ι.app j))⟦(0 : ℤ)⟧') = _
    exact hb j f.down

end AlgebraicGeometry
