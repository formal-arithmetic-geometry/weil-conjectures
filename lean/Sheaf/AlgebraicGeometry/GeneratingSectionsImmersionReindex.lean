/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceReindexIsIso
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan

/-! # Invariance of an immersive generating system under isomorphism and reindexing

Source: Stacks Project, Constructions, Tag 01NE, classification by invertible
modules with generating sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

attribute [local irreducible] homOfGeneratingSections

private noncomputable abbrev sectionFamily {Y : Scheme.{u}} (L : Y.Modules)
    {I : Type u} (s : I → Γ(L, ⊤)) : I → L.sections :=
  fun i ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection L (s i))

private theorem sectionFamily_eval {Y : Scheme.{u}} (L : Y.Modules)
    {I : Type u} (s : I → Γ(L, ⊤)) (i : I) (U : Y.Opens) :
    (sectionFamily L s i).val (Opposite.op U) =
      L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s i) :=
  homOfGlobalSection_app_one L (s i) U

private theorem chart_hom_ext {S : Scheme.{u}} {I : Type u}
    {W : Scheme.{u}} {a b : W ⟶ ℙ(I; S)} (i : I)
    (ha : a ⁻¹ᵁ standardOpen I S i = ⊤) (hb : b ⁻¹ᵁ standardOpen I S i = ⊤)
    (hS : a ≫ ℙ(I; S) ↘ S = b ≫ ℙ(I; S) ↘ S)
    (hr : ∀ j, a.appLE (standardOpen I S i) ⊤ ha.ge (coordRatio I S i j) =
      b.appLE (standardOpen I S i) ⊤ hb.ge (coordRatio I S i j)) : a = b := by
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let z : S ⟶ Z := specULiftZIsTerminal.from S
  have hpre : map I z ⁻¹ᵁ standardOpen I Z i = standardOpen I S i := by
    rw [standardOpen, ← Scheme.Hom.comp_preimage, map_toProjInt]
    rfl
  have ha' : (a ≫ map I z) ⁻¹ᵁ standardOpen I Z i = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hpre, ha]
  have hb' : (b ≫ map I z) ⁻¹ᵁ standardOpen I Z i = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hpre, hb]
  have h : a ≫ map I z = b ≫ map I z := by
    apply hom_ext_of_preimage_standardOpen_eq_top i ha' hb'
    · exact specULiftZIsTerminal.hom_ext _ _
    · intro j
      have ea := Scheme.Hom.appLE_comp_appLE a (map I z)
        (standardOpen I Z i) (standardOpen I S i) ⊤ hpre.ge ha.ge
      have eb := Scheme.Hom.appLE_comp_appLE b (map I z)
        (standardOpen I Z i) (standardOpen I S i) ⊤ hpre.ge hb.ge
      rw [← ea, ← eb, CommRingCat.comp_apply, CommRingCat.comp_apply,
        map_appLE_coordRatio]
      exact hr j
  apply hom_ext I S hS
  simpa only [Category.assoc, map_toProjInt (S := S) (T := Z) I z] using
    congrArg (fun q ↦ q ≫ toProjInt I Z) h

private theorem nativeHom_eq_generatingSections
    {Y S : Scheme.{u}} {I : Type u} [Finite I] (g : Y ⟶ S)
    (L : Y.Modules) [L.IsInvertible] (s : I → L.sections)
    (U : I → Y.Opens)
    (hs : ∀ i, IsFreeGenerator (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
      ((s i).val (Opposite.op ⊤)))) (hU : ⨆ i, U i = ⊤)
    (hgen : Epi (L.freeHomEquiv.symm s)) :
    homOfIsFreeGenerator (fun i ↦ (s i).val (Opposite.op ⊤)) U hs g hU =
      homOfGeneratingSections I g L s hgen := by
  let a : I → Γ(L, ⊤) := fun i ↦ (s i).val (Opposite.op ⊤)
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let φ := homOfIsFreeGenerator a U hs (specULiftZIsTerminal.from Y) hU
  let ε := asIso (twistRestrictHom a U hs (specULiftZIsTerminal.from Y) hU)
  let adj := Classical.choose (exists_tensorPullbackAdjunction φ)
  let c := (adj.leftAdjointUniq (pullbackPushforwardAdjunction φ)).app (twist I Z 1)
  have he : ∃ e : (tensorPullback φ).obj (twist I Z 1) ≅ L,
      ∀ i, e.hom.app ⊤ ((adj.unit.app (twist I Z 1)).val.app (Opposite.op ⊤)
        (twistOneSection I Z i)) = a i := by
    refine ⟨c ≪≫ ε, ?_⟩
    intro i
    have ht : c.hom.app ⊤ ((adj.unit.app (twist I Z 1)).val.app (Opposite.op ⊤)
        (twistOneSection I Z i)) = pullbackSection φ (twistOneSection I Z i) := by
      exact congrArg (fun t ↦ t.val.app (Opposite.op ⊤) (twistOneSection I Z i))
        (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction φ) (twist I Z 1))
    simp only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply]
    erw [ht]
    simpa only [φ, ε, asIso_hom, Scheme.Hom.preimage_top, presheaf_map_id_apply]
      using twistRestrictHom_app_pullbackSection a U hs (specULiftZIsTerminal.from Y) hU i
  have hφ : φ = integralHomOfGeneratingSections I L s hgen :=
    (Classical.choose_spec (generatingSections_integralHom_exists I L s hgen)).2 φ he
  apply (homOfGeneratingSections_spec I g L s hgen).2.2
  · exact homOfIsFreeGenerator_over a U hs g hU
  · rw [← hφ]
    apply Scheme.Opens.hom_ext_of_iSup_eq_top U hU
    intro i
    simp only [φ, a, ι_homOfIsFreeGenerator_assoc, localHom, homOfSections_toProjInt]

private theorem exists_generator_cover {Y : Scheme.{u}} (L : Y.Modules)
    [L.IsInvertible] {I : Type u} [Finite I] (s : I → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (sectionFamily L s))) :
    ∃ U : I → Y.Opens, ∃ _hs : ∀ i, IsFreeGenerator
      (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)), ⨆ i, U i = ⊤ := by
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let φ := integralHomOfGeneratingSections I L (sectionFamily L s) hgen
  obtain ⟨e, he⟩ := integralHomOfGeneratingSections_spec I L (sectionFamily L s) hgen
  let adj := Classical.choose (exists_tensorPullbackAdjunction φ)
  let c := (adj.leftAdjointUniq (pullbackPushforwardAdjunction φ)).app (twist I Z 1)
  let ε : twistRestrict φ 1 ≅ L := c.symm ≪≫ e
  have hε (i : I) : ε.hom.app _ (pullbackSection φ (twistOneSection I Z i)) =
      L.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s i) := by
    have hc : c.hom.app ⊤ ((adj.unit.app (twist I Z 1)).val.app (Opposite.op ⊤)
        (twistOneSection I Z i)) = pullbackSection φ (twistOneSection I Z i) := by
      exact congrArg (fun t ↦ t.val.app (Opposite.op ⊤) (twistOneSection I Z i))
        (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction φ) (twist I Z 1))
    simp only [Scheme.Hom.preimage_top, ε, Iso.trans_hom, Iso.symm_hom, Hom.comp_app,
      ConcreteCategory.comp_apply]
    rw [← hc]
    have hi (x) : c.inv.app ⊤ (c.hom.app ⊤ x) = x := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
      rfl
    rw [hi]
    simpa only [sectionFamily_eval, presheaf_map_id_apply] using he i
  exact ⟨fun i ↦ φ ⁻¹ᵁ standardOpen I Z i,
    fun i ↦ isFreeGenerator_of_twistRestrict_iso ε.hom hε i,
    φ.iSup_preimage_eq_top (iSup_standardOpen I Z)⟩

private theorem reindex_generating {Y : Scheme.{u}} (L : Y.Modules)
    {I J : Type u} [Finite I] [Finite J] (e : J ≃ I) (s : I → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (sectionFamily L s))) :
    Epi (L.freeHomEquiv.symm (sectionFamily L (s ∘ e))) := by
  rw [generating_sections_iff_stalk_span] at hgen ⊢
  intro y
  convert hgen y using 2
  change Set.range ((fun i ↦ TopCat.Presheaf.germ L.val.presheaf ⊤ y trivial
      ((sectionFamily L s i).val (Opposite.op ⊤))) ∘ e) = _
  exact e.surjective.range_comp _


private theorem iso_generating {Y : Scheme.{u}} (M N : Y.Modules) (α : M ≅ N)
    {I : Type u} (s : I → Γ(M, ⊤)) (t : I → Γ(N, ⊤))
    (ht : ∀ i, α.hom.app ⊤ (s i) = t i)
    (hgen : Epi (M.freeHomEquiv.symm (sectionFamily M s))) :
    Epi (N.freeHomEquiv.symm (sectionFamily N t)) := by
  have hf : sectionFamily N t =
      fun i ↦ SheafOfModules.sectionsMap α.hom (sectionFamily M s i) := by
    funext i
    apply PresheafOfModules.sections_ext
    intro U
    change (sectionFamily N t i).val U = α.hom.val.app U ((sectionFamily M s i).val U)
    obtain ⟨U⟩ := U
    rw [sectionFamily_eval, sectionFamily_eval]
    change _ = α.hom.app U _
    rw [Hom.app_presheaf_map, ht]
  rw [hf, ← SheafOfModules.freeHomEquiv_symm_comp]
  have := hgen
  infer_instance

private noncomputable def coordinateReindex {I J : Type u} (e : J ≃ I) (S : Scheme.{u}) :
    ℙ(I; S) ⟶ ℙ(J; S) :=
  ProjectiveSpace.homOfIsFreeGenerator
    (fun j ↦ pullbackSection (𝟙 ℙ(I; S)) (ProjectiveSpace.twistOneSection I S (e j)))
    (fun j ↦ ProjectiveSpace.standardOpen I S (e j))
    (fun j ↦ ProjectiveSpace.isFreeGenerator_pullbackSection_twistOneSection
      (𝟙 ℙ(I; S)) (e j))
    (ℙ(I; S) ↘ S) ((e.iSup_comp).trans (ProjectiveSpace.iSup_standardOpen I S))

private theorem coordinateReindex_isIso {I J : Type u} (e : J ≃ I) (S : Scheme.{u}) :
    IsIso (coordinateReindex e S) :=
  ProjectiveSpace.isIso_homOfIsFreeGenerator_reindex I J e S

attribute [local instance] coordinateReindex_isIso

attribute [local irreducible] ProjectiveSpace.homOfIsFreeGenerator

private theorem nativeHom_iso_reindex
    {Y S : Scheme.{u}} {I J : Type u} (e : J ≃ I)
    (g : Y ⟶ S) (L N : Y.Modules) (α : L ≅ N)
    (s : I → Γ(L, ⊤)) (t : J → Γ(N, ⊤))
    (ht : ∀ j, α.hom.app ⊤ (s (e j)) = t j) (U : I → Y.Opens)
    (hs : ∀ i, IsFreeGenerator (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)))
    (hU : ⨆ i, U i = ⊤)
    (hsN : ∀ j, IsFreeGenerator
      (N.presheaf.map (homOfLE (le_top : U (e j) ≤ ⊤)).op (t j))) :
    ProjectiveSpace.homOfIsFreeGenerator s U hs g hU ≫ coordinateReindex e S =
      ProjectiveSpace.homOfIsFreeGenerator t (fun j ↦ U (e j)) hsN g
        ((e.iSup_comp).trans hU) := by
  let H := ProjectiveSpace.homOfIsFreeGenerator s U hs g hU
  let R := coordinateReindex e S
  let H' := ProjectiveSpace.homOfIsFreeGenerator t (fun j ↦ U (e j)) hsN g ((e.iSup_comp).trans hU)
  have hR (i : J) := ProjectiveSpace.le_preimage_standardOpen
    (fun j ↦ pullbackSection (𝟙 ℙ(I; S)) (ProjectiveSpace.twistOneSection I S (e j)))
    (fun j ↦ ProjectiveSpace.standardOpen I S (e j))
    (fun j ↦ ProjectiveSpace.isFreeGenerator_pullbackSection_twistOneSection
      (𝟙 ℙ(I; S)) (e j))
    (ℙ(I; S) ↘ S) ((e.iSup_comp).trans (ProjectiveSpace.iSup_standardOpen I S)) i
  have hr (i j : J) : R.appLE (ProjectiveSpace.standardOpen J S i)
      (ProjectiveSpace.standardOpen I S (e i))
      (hR i)
      (ProjectiveSpace.coordRatio J S i j) = ProjectiveSpace.coordRatio I S (e i) (e j) := by
    dsimp only [R, coordinateReindex]
    rw [ProjectiveSpace.homOfIsFreeGenerator_appLE_coordRatio]
    apply (ProjectiveSpace.isFreeGenerator_pullbackSection_twistOneSection
      (𝟙 ℙ(I; S)) (e i)).coeff_eq_iff _ _ |>.mpr
    symm
    have ht := ProjectiveSpace.pullbackSection_twistOneSection_map_eq_smul
      (𝟙 ℙ(I; S)) (e j) (e i)
    rw [Scheme.Hom.id_app] at ht
    exact ht
  apply Scheme.Opens.hom_ext_of_iSup_eq_top (fun j ↦ U (e j)) ((e.iSup_comp).trans hU)
  intro i
  have hH := ProjectiveSpace.le_preimage_standardOpen s U hs g hU (e i)
  have hH' := ProjectiveSpace.le_preimage_standardOpen t (fun j ↦ U (e j)) hsN g
    ((e.iSup_comp).trans hU) i
  have hι : ⊤ ≤ (U (e i)).ι ⁻¹ᵁ U (e i) := fun x _ ↦ x.2
  have hp₁ : ((U (e i)).ι ≫ H ≫ R) ⁻¹ᵁ
      ProjectiveSpace.standardOpen J S i = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    apply eq_top_iff.mpr
    intro x _
    exact hR i (hH x.2)
  have hp₂ : ((U (e i)).ι ≫ H') ⁻¹ᵁ
      ProjectiveSpace.standardOpen J S i = ⊤ := by
    rw [Scheme.Hom.comp_preimage]
    exact eq_top_iff.mpr (fun x _ ↦ hH' x.2)
  apply chart_hom_ext i hp₁ hp₂
  · dsimp only [H, R, H', coordinateReindex]
    simp only [Category.assoc, ProjectiveSpace.homOfIsFreeGenerator_over]
  · intro j
    have hleft (p) : ((U (e i)).ι ≫ H ≫ R).appLE
        (ProjectiveSpace.standardOpen J S i) ⊤ p (ProjectiveSpace.coordRatio J S i j) =
        (U (e i)).ι.appLE (U (e i)) ⊤ hι
          (H.appLE (ProjectiveSpace.standardOpen I S (e i)) (U (e i)) hH
            (R.appLE (ProjectiveSpace.standardOpen J S i)
              (ProjectiveSpace.standardOpen I S (e i)) (hR i)
                (ProjectiveSpace.coordRatio J S i j))) := by
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    have hright (p) : ((U (e i)).ι ≫ H').appLE
        (ProjectiveSpace.standardOpen J S i) ⊤ p (ProjectiveSpace.coordRatio J S i j) =
        (U (e i)).ι.appLE (U (e i)) ⊤ hι
          (H'.appLE (ProjectiveSpace.standardOpen J S i) (U (e i)) hH'
            (ProjectiveSpace.coordRatio J S i j)) := by
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    rw [hleft, hright, hr]
    dsimp only [H, H']
    rw [ProjectiveSpace.homOfIsFreeGenerator_appLE_coordRatio]
    apply congrArg ((U (e i)).ι.appLE (U (e i)) ⊤ hι)
    rw [ProjectiveSpace.homOfIsFreeGenerator_appLE_coordRatio t
      (fun j ↦ U (e j)) hsN g ((e.iSup_comp).trans hU) i j]
    symm
    apply (hsN i).coeff_eq_iff _ _ |>.mpr
    have h := congrArg (α.hom.app (U (e i)))
      (ProjectiveSpace.sectionRatio_smul s U hs (e i) (e j))
    rw [Hom.app_smul, Hom.app_presheaf_map, Hom.app_presheaf_map, ht, ht] at h
    exact h

/-- Isomorphic invertible modules and equivalent finite index sets describe the same
immersive linear system.

Source: Stacks Project, Constructions, Tag 01NE; the basis change in paragraph 2 of
blueprint `lem-zl-bertini-finite-cover-curve.proof.md`.
(blueprint: lem-zl-generating-sections-immersion-iso-reindex).

Proof: The equivalence of index sets identifies the two free modules, and the
section-preserving module isomorphism identifies their evaluation maps. Thus the
second evaluation map is an epimorphism. Permuting the homogeneous variables
induces an isomorphism between the two projective spaces over the base. The
classification of projective morphisms by an invertible module with generating
sections identifies the second morphism with the first followed by this
isomorphism. Immersions are preserved under composition with an isomorphism.
These arguments also apply to the empty index set: generation then forces the
source scheme to be empty, and both morphisms are immersions.
-/
theorem generatingSections_immersion_iso_reindex
    {X B : Scheme.{u}} (f : X ⟶ B)
    {I J : Type u} [Finite I] [Finite J] (e : J ≃ I)
    (M N : X.Modules) [M.IsInvertible] [N.IsInvertible] (α : M ≅ N)
    (s : I → Γ(M, ⊤)) (t : J → Γ(N, ⊤))
    (ht : ∀ j, α.hom.app ⊤ (s (e j)) = t j)
    (hs : ∃ h : Epi (M.freeHomEquiv.symm
        (fun i ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection M (s i)))),
      IsImmersion (@homOfGeneratingSections I inferInstance X B f M inferInstance
        (fun i ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection M (s i))) h)) :
    ∃ h : Epi (N.freeHomEquiv.symm
        (fun j ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection N (t j)))),
      IsImmersion (@homOfGeneratingSections J inferInstance X B f N inferInstance
        (fun j ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection N (t j))) h) := by
  classical
  obtain ⟨hgen, himm⟩ := hs
  have hgen' := reindex_generating M e s hgen
  have htgen := iso_generating M N α (s ∘ e) t ht hgen'
  refine ⟨htgen, ?_⟩
  obtain ⟨U, hUgen, hU⟩ := exists_generator_cover M s hgen
  have hN (j : J) : IsFreeGenerator
      (N.presheaf.map (homOfLE (le_top : U (e j) ≤ ⊤)).op (t j)) := by
    have h := (hUgen (e j)).app_hom α
    rwa [Hom.app_presheaf_map, ht] at h
  have h := nativeHom_iso_reindex e f M N α s t ht U hUgen hU hN
  have hsf (i : I) : (sectionFamily M s i).val (Opposite.op ⊤) = s i := by
    rw [sectionFamily_eval, presheaf_map_id_apply]
  have htf (j : J) : (sectionFamily N t j).val (Opposite.op ⊤) = t j := by
    rw [sectionFamily_eval, presheaf_map_id_apply]
  have hM := nativeHom_eq_generatingSections f M (sectionFamily M s) U
    (by simpa only [hsf] using hUgen) hU hgen
  have hN' := nativeHom_eq_generatingSections f N (sectionFamily N t) (fun j ↦ U (e j))
    (fun j ↦ by simpa only [htf] using hN j) ((e.iSup_comp).trans hU) htgen
  simp only [hsf] at hM
  simp only [htf] at hN'
  rw [hM, hN'] at h
  rw [← h]
  have := himm
  infer_instance

end AlgebraicGeometry.ProjectiveSpace
