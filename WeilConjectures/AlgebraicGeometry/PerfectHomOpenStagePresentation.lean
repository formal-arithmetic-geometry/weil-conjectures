/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenStageData
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenStageMaps

/-! # Local presentations of shifted open Hom systems

## References

* Stacks Project, Tags 09RE, 079W, 08FE and 0D5S.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Restriction of a representing Hom system to one compact open, before taking
any colimit. This supplies stage and apex equivalences and their transport equations
(Stacks, Tags 09RE, 079W, 08FE and 0D5S). -/
theorem perfect_hom_open_stage_presentation
    {I : Type u} [Preorder I]
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
    (h : PerfectHomPushPullData R c s Q F d) (n : ℤ) :
    let H := schemeMVDerivedRestriction Y (t ⁻¹ᵁ W) ⋙
      schemeDerivedDirectImage (t ⁻¹ᵁ W).ι
    ∃ (Z : Scheme.{u}) (k : Z ⟶ X) (_ : IsOpenImmersion k),
      k.opensRange = W ∧
    ∃ (s' : Z ⟶ Spec (R.obj i)), s' = k ≫ s₀ ∧
    ∃ (_ : LocallyOfFinitePresentation s') (_ : QuasiCompact s') (_ : QuasiSeparated s')
      (_ : ∀ T : Z.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over T)))
      (P' Q' : schemeDerivedCategory Z), Z.IsPerfect P' ∧ Z.IsPerfect Q' ∧
    ∃ (e : ∀ j : Set.Ici i, (P ⟶ (H.obj (F.obj j))⟦n⟧) ≃
        ((derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj P' ⟶
         (derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj Q'))
      (b : (P ⟶ (H.obj d.pt)⟦n⟧) ≃
        ((derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj P' ⟶
         (derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj Q')),
      (∀ (j l : Set.Ici i) (hjl : j ≤ l) (f : P ⟶ (H.obj (F.obj j))⟦n⟧),
        e l (f ≫ (H.map (F.map (homOfLE hjl)))⟦n⟧') =
          perfectStageMap R s' j.property hjl (e j f)) ∧
      (∀ (j : Set.Ici i) (f : P ⟶ (H.obj (F.obj j))⟦n⟧),
        b (f ≫ (H.map (d.ι.app j))⟦n⟧') =
          perfectLimitMap R c s' j.property (e j f)) := by
  classical
  dsimp
  let B := t ⁻¹ᵁ W
  have hcomp : QuasiCompact (t ≫ s₀) := hs ▸ inferInstance
  have : QuasiCompact t := QuasiCompact.of_comp t s₀
  have hB : IsCompact (B : Set Y) := t.isCompact_preimage hW
  let : CompactSpace B.toScheme := isCompact_iff_compactSpace.mp hB
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated s
  have : QuasiCompact B.ι := inferInstance
  obtain ⟨hcat, hp', hq'⟩ := Scheme.perfect_hom_open_stage_data Y B P Q hP hQ n
  let := hcat
  refine ⟨B.toScheme, B.ι ≫ t, inferInstance, ?_, B.ι ≫ s, ?_,
    inferInstance, inferInstance, inferInstance, hcat,
    ((schemeMVDerivedRestriction Y B).obj P)⟦-n⟧,
    (schemeMVDerivedRestriction Y B).obj Q, hp', hq', ?_⟩
  · rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr ht]
  · rw [hs, Category.assoc]
  · exact perfect_hom_open_stage_maps R c i X W Y t s P Q F d h n

end AlgebraicGeometry
