/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceReindexIsIso
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-!
# Smooth general members of an immersive linear system

Source: Stacks Project, Varieties, Situation 0FD3 and Lemma 0FD6
(blueprint: lem-zl-bertini-smooth-member).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

noncomputable section

/-- The coefficient point of affine space defined by a tuple over an extension field.
Source: Stacks Project, Situation 0FD3 (blueprint: lem-zl-bertini-smooth-member). -/
def bertiniCoefficientPoint {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type u} (a : I → K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (MvPolynomial I k)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap k K) a))

/-- The section `∑ aᵢ ψ(vᵢ)` on the field base change of `Y`, using the canonical
module-pullback unit. Scalars act through the projection to `Spec K`.
Source: Stacks Project, Situation 0FD3 (blueprint: lem-zl-bertini-smooth-member). -/
def bertiniMemberSection {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (a : I → K) :
    Γ((Scheme.Modules.tensorPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L, ⊤) :=
  ∑ i, (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (a i)) •
    Scheme.Modules.tensorSectionsUnit
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L
        (s i)

/-- A family of top-open sections as compatible global sections, through the existing
unit/global-section equivalence. Source: Stacks Project, Situation 0FD3
(blueprint: lem-zl-bertini-smooth-member). -/
def bertiniSectionFamily {Y : Scheme.{u}} (L : Y.Modules) {I : Type u}
    (s : I → Γ(L, ⊤)) : I → L.sections :=
  fun i ↦ (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (s i))

open Scheme.Modules

private def tensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ Scheme.Modules.pullback f :=
  (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)

attribute [local irreducible] tensorPullback tensorPullbackObj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback f).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  erw [hi, ((tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (r : Γ(Y, ⊤)) (s : Γ(M, ⊤)) :
    tensorSectionsUnit f M (r • s) = f.appTop r • tensorSectionsUnit f M s := by
  rw [tensorUnit_eq]
  exact Hom.app_smul _ r s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((tensorSectionsComp a b).hom.app M).app ⊤
      (tensorSectionsUnit a _ (tensorSectionsUnit b M s)) =
        tensorSectionsUnit (a ≫ b) M s := by
  have hu := congrArg (fun t ↦ t.app ⊤)
    (unit_conjugateEquiv_symm
      (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b)))
      ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
        (Classical.choose (exists_tensorPullbackAdjunction a)))
      (pushforwardComp a b).inv M)
  rw [tensorUnit_eq, tensorUnit_eq, tensorUnit_eq]
  simp only [Adjunction.comp_unit_app, Hom.comp_app, pushforward_map_app,
    Functor.comp_map, pushforwardComp_inv_app_app] at hu
  exact (ConcreteCategory.congr_hom hu s).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : Γ(M, ⊤)) :
    ((tensorComparison f).hom.app M).app ⊤
      (tensorSectionsUnit f M s) = pullbackSection f s := by
  rw [tensorUnit_eq]
  exact congrArg (fun t ↦ t.app ⊤ s)
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction f) M)

private theorem zeroLocus_section_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (s : Γ(M, ⊤)) :
    (homOfGlobalSection N (e.hom.app ⊤ s)).zeroLocus =
      (homOfGlobalSection M s).zeroLocus := by
  have h : homOfGlobalSection M s ≫ e.hom =
      homOfGlobalSection N (e.hom.app ⊤ s) := by
    apply unit_hom_ext
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, homOfGlobalSection_app_one,
      presheaf_map_id_apply]
  exact Hom.zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk (Iso.refl _) e.symm (by
      change 𝟙 _ ≫ homOfGlobalSection M s =
        homOfGlobalSection N (e.hom.app ⊤ s) ≫ e.inv
      rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zeroLocus_tensorUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] (s : Γ(M, ⊤)) :
    (homOfGlobalSection M s).zeroLocus.comap f =
      (homOfGlobalSection ((tensorPullback f).obj M) (tensorSectionsUnit f M s)).zeroLocus := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u} (unit Y) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ Y.Modules)
  rw [Hom.comap_zeroLocus]
  let e := (tensorComparison f).app M
  have he := zeroLocus_section_iso e (tensorSectionsUnit f M s)
  change (homOfGlobalSection _
    (((tensorComparison f).hom.app M).app ⊤ (tensorSectionsUnit f M s))).zeroLocus = _ at he
  rw [tensorUnit_comparison] at he
  rw [← he]
  apply Hom.zeroLocus_eq_of_arrowIso _ _
  refine Arrow.isoMk (pullbackObjUnitIso f) (Iso.refl _) ?_
  change (pullbackObjUnitIso f).hom ≫
    homOfGlobalSection _ (pullbackSection f s) =
      (Scheme.Modules.pullback f).map (homOfGlobalSection M s) ≫ 𝟙 _
  symm
  rw [Category.comp_id]
  rw [← cancel_epi (pullbackObjUnitIso f).inv, Iso.inv_hom_id_assoc]
  apply unit_hom_ext
  have h := pullbackSection_app_one f (homOfGlobalSection M s)
  simpa only [Scheme.Hom.preimage_top, homOfGlobalSection_app_one,
    presheaf_map_id_apply] using h.symm

private theorem tensorPullback_invertible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] : ((tensorPullback f).obj M).IsInvertible :=
  IsInvertible.of_iso ((tensorComparison f).app M).symm

private theorem coefficientPoint_comp {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type u} (a : I → K) :
    bertiniCoefficientPoint (k := k) a ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [bertiniCoefficientPoint, ← Spec.map_comp]
  congr 1
  ext c
  exact MvPolynomial.eval₂_C _ _ c

private def memberToUniversalAmbient {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) {I : Type u} (a : I → K) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
      pullback (Spec.map
        (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f :=
  pullback.lift
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
      bertiniCoefficientPoint (k := k) a)
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (by rw [Category.assoc, coefficientPoint_comp, pullback.condition])

private theorem memberToUniversalAmbient_isPullback
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) {I : Type u} (a : I → K) :
    IsPullback (memberToUniversalAmbient f a)
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.fst (Spec.map
        (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f)
      (bertiniCoefficientPoint (k := k) a) := by
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback _ _).flip)
  · simpa only [memberToUniversalAmbient, pullback.lift_snd, coefficientPoint_comp] using
      (IsPullback.of_hasPullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  · exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zeroLocus_tensorUnit_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) [M.IsInvertible]
    (s : Γ((tensorPullback b).obj M, ⊤)) :
    (homOfGlobalSection _ s).zeroLocus.comap a =
      (homOfGlobalSection _ (((tensorSectionsComp a b).hom.app M).app ⊤
        (tensorSectionsUnit a _ s))).zeroLocus := by
  have := tensorPullback_invertible b M
  rw [zeroLocus_tensorUnit]
  exact (zeroLocus_section_iso ((tensorSectionsComp a b).app M)
    (tensorSectionsUnit a _ s)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zeroLocus_sum_triangle {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (p : a ≫ b = c)
    (M : Z.Modules) [M.IsInvertible] {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) (r : I → Γ(Y, ⊤)) (t : I → Γ(X, ⊤))
    (hr : ∀ i, a.appTop (r i) = t i) :
    (homOfGlobalSection _ (∑ i, r i • tensorSectionsUnit b M (s i))).zeroLocus.comap a =
      (homOfGlobalSection _ (∑ i, t i • tensorSectionsUnit c M (s i))).zeroLocus := by
  subst c
  rw [zeroLocus_tensorUnit_comp]
  congr 1
  congr 1
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorUnit_smul, Hom.app_smul, tensorUnit_comp, hr]

private theorem universalIdeal_comap_member
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
    (L : Y.Modules) [L.IsInvertible] {I : Type u} [Fintype I]
    (s : I → Γ(L, ⊤)) (a : I → K) :
    (bertiniUniversalIdeal f L s).comap (memberToUniversalAmbient f a) =
      (homOfGlobalSection _ (bertiniMemberSection f L s a)).zeroLocus := by
  apply zeroLocus_sum_triangle
    (memberToUniversalAmbient f a) _ _ (pullback.lift_snd _ _ _) L s
  intro i
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  change ((memberToUniversalAmbient f a) ≫ pullback.fst _ _).appTop _ = _
  rw [memberToUniversalAmbient, pullback.lift_fst, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, bertiniCoefficientPoint, Scheme.specMap_appTop_ΓSpecIso_inv]
  congr 1
  congr 1
  exact MvPolynomial.eval₂_X _ _ i

private theorem smooth_of_isPullback_locally
    {Z T H A : Scheme.{u}} {α : Z ⟶ H} {g : Z ⟶ T} {q : H ⟶ A} {a : T ⟶ A}
    (h : IsPullback α g q a)
    (hloc : ∀ z : Z, ∃ W : H.Opens, α z ∈ W ∧ Smooth (W.ι ≫ q)) : Smooth g := by
  classical
  choose W hz hW using hloc
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun z : Z ↦ α ⁻¹ᵁ W z)
  · apply eq_top_iff.mpr
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hz z⟩
  · intro z
    exact MorphismProperty.of_isPullback
      ((isPullback_morphismRestrict α (W z)).paste_vert h) (hW z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHom_eq_generatingSections
    {Y S : Scheme.{u}} {I : Type u} [Finite I] (g : Y ⟶ S)
    (L : Y.Modules) [L.IsInvertible] (s : I → Γ(L, ⊤))
    (U : I → Y.Opens)
    (hs : ∀ i, IsFreeGenerator (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)))
    (hU : ⨆ i, U i = ⊤)
    (hgen : Epi (L.freeHomEquiv.symm (bertiniSectionFamily L s))) :
    ProjectiveSpace.homOfIsFreeGenerator s U hs g hU =
      ProjectiveSpace.homOfGeneratingSections I g L (bertiniSectionFamily L s) hgen := by
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let φ := ProjectiveSpace.homOfIsFreeGenerator s U hs (specULiftZIsTerminal.from Y) hU
  let ε := asIso (ProjectiveSpace.twistRestrictHom s U hs
    (specULiftZIsTerminal.from Y) hU)
  have he : ∃ e : (tensorPullback φ).obj (ProjectiveSpace.twist I Z 1) ≅ L,
      ∀ i, e.hom.app ⊤ (((Classical.choose (exists_tensorPullbackAdjunction φ)).unit.app
        (ProjectiveSpace.twist I Z 1)).val.app (op ⊤)
          (ProjectiveSpace.twistOneSection I Z i)) =
        (bertiniSectionFamily L s i).val (op ⊤) := by
    refine ⟨(tensorComparison φ).app _ ≪≫ ε, ?_⟩
    intro i
    have ht := tensorUnit_comparison φ (ProjectiveSpace.twist I Z 1)
      (ProjectiveSpace.twistOneSection I Z i)
    rw [tensorUnit_eq] at ht
    simp only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply]
    erw [ht]
    have hh := ProjectiveSpace.twistRestrictHom_app_pullbackSection s U hs
      (specULiftZIsTerminal.from Y) hU i
    have hfamily : (bertiniSectionFamily L s i).val (op ⊤) = s i := by
      change (SheafOfModules.unitHomEquiv L (homOfGlobalSection L (s i))).val (op ⊤) = _
      exact (homOfGlobalSection_app_one L (s i) ⊤).trans (presheaf_map_id_apply _ _)
    rw [hfamily]
    simpa only [φ, ε, Z, asIso_hom, Scheme.Hom.preimage_top,
      presheaf_map_id_apply] using hh
  have hφ : φ = ProjectiveSpace.integralHomOfGeneratingSections I L
      (bertiniSectionFamily L s) hgen :=
    (Classical.choose_spec (ProjectiveSpace.generatingSections_integralHom_exists
      I L (bertiniSectionFamily L s) hgen)).2 φ he
  apply (ProjectiveSpace.homOfGeneratingSections_spec I g L
    (bertiniSectionFamily L s) hgen).2.2
  · exact ProjectiveSpace.homOfIsFreeGenerator_over s U hs g hU
  · rw [← hφ]
    apply Scheme.Opens.hom_ext_of_iSup_eq_top U hU
    intro i
    simp only [φ, ProjectiveSpace.ι_homOfIsFreeGenerator_assoc,
      ProjectiveSpace.localHom, ProjectiveSpace.homOfSections_toProjInt]

private def coordinateReindex {I J : Type u} (e : J ≃ I) (S : Scheme.{u}) :
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

private theorem nativeHom_reindex
    {Y S : Scheme.{u}} [IsAffine S] {I J : Type u} (e : J ≃ I)
    (g : Y ⟶ S) (L : Y.Modules) (s : I → Γ(L, ⊤)) (U : I → Y.Opens)
    (hs : ∀ i, IsFreeGenerator (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)))
    (hU : ⨆ i, U i = ⊤) :
    ProjectiveSpace.homOfIsFreeGenerator s U hs g hU ≫ coordinateReindex e S =
      ProjectiveSpace.homOfIsFreeGenerator (s ∘ e) (U ∘ e) (fun j ↦ hs (e j)) g
        ((e.iSup_comp).trans hU) := by
  let H := ProjectiveSpace.homOfIsFreeGenerator s U hs g hU
  let R := coordinateReindex e S
  let H' := ProjectiveSpace.homOfIsFreeGenerator (s ∘ e) (U ∘ e)
    (fun j ↦ hs (e j)) g ((e.iSup_comp).trans hU)
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
  apply Scheme.Opens.hom_ext_of_iSup_eq_top (U ∘ e) ((e.iSup_comp).trans hU)
  intro i
  have hH := ProjectiveSpace.le_preimage_standardOpen s U hs g hU (e i)
  have hH' := ProjectiveSpace.le_preimage_standardOpen (s ∘ e) (U ∘ e)
    (fun j ↦ hs (e j)) g ((e.iSup_comp).trans hU) i
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
  apply ProjectiveSpace.hom_ext_of_preimage_standardOpen_eq_top i hp₁ hp₂
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
    dsimp only [H]
    rw [ProjectiveSpace.homOfIsFreeGenerator_appLE_coordRatio]
    apply congrArg ((U (e i)).ι.appLE (U (e i)) ⊤ hι)
    exact (ProjectiveSpace.homOfIsFreeGenerator_appLE_coordRatio (s ∘ e) (U ∘ e)
      (fun j ↦ hs (e j)) g ((e.iSup_comp).trans hU) i j).symm

private theorem exists_generator_cover {Y : Scheme.{u}} (L : Y.Modules)
    [L.IsInvertible] {I : Type u} [Finite I] (s : I → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (bertiniSectionFamily L s))) :
    ∃ U : I → Y.Opens, ∃ _hs : ∀ i, IsFreeGenerator
      (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)), ⨆ i, U i = ⊤ := by
  classical
  have hnonvan : ∀ y : Y, ∃ i, y ∈ nonvanishingLocus L (s i) := by
    intro y
    obtain ⟨e⟩ := invertible_stalk_linearEquiv Y L y
    have hfamily (i : I) : (bertiniSectionFamily L s i).val (op ⊤) = s i := by
      exact (homOfGlobalSection_app_one L (s i) ⊤).trans (presheaf_map_id_apply _ _)
    have hspan := (generating_sections_iff_stalk_span Y L (bertiniSectionFamily L s)).mp hgen y
    simp only [hfamily] at hspan
    by_contra! hn
    let P : Submodule (Y.presheaf.stalk y) ↑(TopCat.Presheaf.stalk L.val.presheaf y) :=
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) • ⊤
    have hle : Submodule.span (Y.presheaf.stalk y)
        (Set.range fun i ↦ TopCat.Presheaf.germ L.val.presheaf ⊤ y trivial (s i)) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact not_not.mp (hn i)
    have hm : P.map e.toLinearMap = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      simp only [P, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
        Ideal.smul_eq_mul, Ideal.mul_top]
    have h1 : (1 : Y.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rw [← hm]
      exact ⟨e.symm 1, hle (hspan ▸ Submodule.mem_top), e.apply_symm_apply 1⟩
    exact (IsLocalRing.maximalIdeal.isMaximal (Y.presheaf.stalk y)).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  let U : I → Y.Opens := fun i ↦
    (Hom.zeroLocus (homOfGlobalSection L (s i))).support.compl
  have hU : ⨆ i, U i = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨i, hi⟩ := hnonvan y
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    rwa [nonvanishingLocus_eq_compl_support_zeroLocus] at hi
  have hgen (i : I) : IsFreeGenerator
      (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)) := by
    have h := isFreeGenerator_app_one_of_le (homOfGlobalSection L (s i)) (U := U i) le_rfl
    change IsFreeGenerator ((homOfGlobalSection L (s i)).app (U i)
      (show Γ(Y, U i) from 1)) at h
    rwa [homOfGlobalSection_app_one] at h
  exact ⟨U, hgen, hU⟩

private theorem reindex_generating {Y : Scheme.{u}} (L : Y.Modules)
    {I J : Type u} [Finite I] [Finite J] (e : J ≃ I) (s : I → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (bertiniSectionFamily L s))) :
    Epi (L.freeHomEquiv.symm (bertiniSectionFamily L (s ∘ e))) := by
  rw [generating_sections_iff_stalk_span] at hgen ⊢
  intro y
  convert hgen y using 2
  change Set.range ((fun i ↦ TopCat.Presheaf.germ L.val.presheaf ⊤ y trivial
      ((bertiniSectionFamily L s i).val (op ⊤))) ∘ e) = _
  exact e.surjective.range_comp _

private theorem reindex_immersion {Y S : Scheme.{u}} [IsAffine S]
    {I J : Type u} [Finite I] [Finite J] (e : J ≃ I)
    (g : Y ⟶ S) (L : Y.Modules) [L.IsInvertible] (s : I → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (bertiniSectionFamily L s)))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections I g L
      (bertiniSectionFamily L s) hgen)] :
    IsImmersion (ProjectiveSpace.homOfGeneratingSections J g L
      (bertiniSectionFamily L (s ∘ e)) (reindex_generating L e s hgen)) := by
  obtain ⟨U, hs, hU⟩ := exists_generator_cover L s hgen
  have h := nativeHom_reindex e g L s U hs hU
  rw [nativeHom_eq_generatingSections g L s U hs hU hgen,
    nativeHom_eq_generatingSections g L (s ∘ e) (U ∘ e) (fun j ↦ hs (e j))
      ((e.iSup_comp).trans hU) (reindex_generating L e s hgen)] at h
  rw [← h]
  infer_instance

private theorem smooth_member_of_avoids_singular_image
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
    (L : Y.Modules) [L.IsInvertible] {I : Type u} [Fintype I]
    (s : I → Γ(L, ⊤)) (a : I → K)
    (ha : ∀ h ∈ bertiniUniversalSingularLocus f L s,
      bertiniUniversalProjection f L s h ∉
        Set.range (bertiniCoefficientPoint (k := k) a)) :
    Smooth ((homOfGlobalSection _ (bertiniMemberSection f L s a)).zeroLocus.subschemeι ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  classical
  let J := (bertiniUniversalIdeal f L s).comap (memberToUniversalAmbient f a)
  have hJ := universalIdeal_comap_member f L s a
  have hp := ((bertiniUniversalIdeal f L s).isPullback_comap
    (memberToUniversalAmbient f a)).flip.paste_vert
      (memberToUniversalAmbient_isPullback f a)
  change IsPullback _ (J.subschemeι ≫ _) (bertiniUniversalProjection f L s) _ at hp
  rw [← hJ]
  apply smooth_of_isPullback_locally hp
  intro z
  by_contra hn
  apply ha _ hn
  refine ⟨(J.subschemeι ≫ pullback.snd f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))) z, ?_⟩
  exact congrArg (fun t ↦ t z) hp.w.symm

private theorem exists_open_smooth_finite_coordinates
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible]
    {V : Type u} [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (ULift.{u} (Fin r)) k V) (ψ : V →+ Γ(L, ⊤))
    (hlinear : ∀ (c : k) (v : V), ψ (c • v) =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) • ψ v)
    (hgen : Epi (L.freeHomEquiv.symm (bertiniSectionFamily L (fun i ↦ ψ (b i)))))
    [hImm : IsImmersion (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin r)) f L
      (bertiniSectionFamily L (fun i ↦ ψ (b i))) hgen)] :
    ∃ U : (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin r)) k))).Opens,
      (U : Set (Spec (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin r)) k)))).Nonempty ∧
      ∀ (K : Type u) [Field K] [Algebra k K] (a : ULift.{u} (Fin r) → K),
        Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (U : Set _) →
        Smooth ((homOfGlobalSection _
          (bertiniMemberSection f L (fun i ↦ ψ (b i)) a)).zeroLocus.subschemeι ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  classical
  have hImm : IsImmersion (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin r))
      f L (fun i ↦ (SheafOfModules.unitHomEquiv L)
        (homOfGlobalSection L (ψ (b i)))) hgen) := by
    exact hImm
  obtain ⟨-, B, hB, hproper, himage⟩ :=
    bertini_singularLocus_dimension_lt f L r b ψ hlinear hgen
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, ?_, ?_⟩
  · exact Set.nonempty_compl.mpr hproper
  · intro K _ _ a ha
    apply smooth_member_of_avoids_singular_image
    intro h hh hv
    exact ha hv (himage (Set.mem_image_of_mem _ hh))

private def coefficientReindex {k : Type u} [Field k] {I J : Type u} (e : J ≃ I) :
    Spec (CommRingCat.of (MvPolynomial I k)) ≅
      Spec (CommRingCat.of (MvPolynomial J k)) :=
  Scheme.Spec.mapIso (MvPolynomial.renameEquiv k e).toRingEquiv.toCommRingCatIso.op

private theorem coefficientPoint_reindex {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I J : Type u} (e : J ≃ I) (a : I → K) :
    bertiniCoefficientPoint (k := k) a ≫ (coefficientReindex (k := k) e).hom =
      bertiniCoefficientPoint (k := k) (a ∘ e) := by
  have heval : CommRingCat.ofHom (MvPolynomial.rename e).toRingHom ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap k K) a) =
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap k K) (a ∘ e)) := by
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.eval₂Hom (algebraMap k K) a
        (MvPolynomial.rename e (MvPolynomial.C c)) =
          MvPolynomial.eval₂Hom (algebraMap k K) (a ∘ e) (MvPolynomial.C c)
      simp only [MvPolynomial.rename_C, MvPolynomial.eval₂Hom_C]
    · intro i
      change MvPolynomial.eval₂Hom (algebraMap k K) a
        (MvPolynomial.rename e (MvPolynomial.X i)) = _
      rw [MvPolynomial.rename_X]
      simp only [CommRingCat.hom_ofHom, MvPolynomial.eval₂Hom_X', Function.comp_apply]
  unfold bertiniCoefficientPoint coefficientReindex
  rw [Scheme.Spec.mapIso_hom]
  change Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap k K) a)) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename e).toRingHom) = _
  rw [← Spec.map_comp, heval]

private theorem memberSection_reindex {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I J : Type u} [Fintype I] [Fintype J] (e : J ≃ I)
    (s : I → Γ(L, ⊤)) (a : I → K) :
    bertiniMemberSection f L (s ∘ e) (a ∘ e) = bertiniMemberSection f L s a := by
  unfold bertiniMemberSection
  exact e.sum_comp (fun i ↦
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (a i)) •
        tensorSectionsUnit
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L (s i))

/-- An immersive generated linear system on a smooth scheme has smooth general members.
The additive map `ψ`, together with its displayed scalar law, is precisely a `k`-linear map
into global sections with the scalar action induced by `f`. A basis indexed by a finite set
expresses finite dimensionality. The single nonempty open works for all extension fields and tuples.

Source: Stacks Project, Varieties, Situation 0FD3 and Lemma 0FD6
(blueprint: lem-zl-bertini-smooth-member).

Proof:
1. Form the universal section `∑ xᵢ ψ(bᵢ)` on affine space times `Y`. Its zero scheme has
   fibre `Z(∑ aᵢ ψ(bᵢ))`, by zero-scheme formation and base change
   (`def-pc-zero-scheme`, `def-pc-base-change`).
2. The non-smooth locus of its projection to affine space has image in a proper closed
   subset, by `lem-zl-bertini-singular-locus-dimension` (Stacks 0FD6).
3. On the complementary open, the projection is smooth: use smoothness local on the source
   (`lem-weil-pbc-smooth-local-on-source`). Smooth base change
   (`lem-pc-proper-base-change`, clause 2) makes every field-valued fibre smooth.
4. The complement is nonempty. The universal-family fibre identification makes this same
   open work over every extension field, exactly the meaning of general in Situation 0FD3.
-/
theorem exists_open_smooth_bertiniMember
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible]
    {V : Type u} [AddCommGroup V] [Module k V] {I : Type u} [Fintype I]
    (b : Module.Basis I k V) (ψ : V →+ Γ(L, ⊤))
    (_hlinear : ∀ (c : k) (v : V),
      ψ (c • v) =
        f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) • ψ v)
    (hgen : Epi (L.freeHomEquiv.symm (bertiniSectionFamily L (fun i ↦ ψ (b i)))))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections I f L
      (bertiniSectionFamily L (fun i ↦ ψ (b i))) hgen)] :
    ∃ U : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
      (U : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
      ∀ (K : Type u) [Field K] [Algebra k K] (a : I → K),
        Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (U : Set _) →
        Smooth ((Scheme.Modules.homOfGlobalSection
          ((Scheme.Modules.tensorPullback
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L)
          (bertiniMemberSection f L (fun i ↦ ψ (b i)) a)).zeroLocus.subschemeι ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  classical
  let e : ULift.{u} (Fin (Fintype.card I)) ≃ I :=
    Equiv.ulift.trans (Fintype.equivFin I).symm
  let s : I → Γ(L, ⊤) := fun i ↦ ψ (b i)
  have hsections : (fun i ↦ ψ ((b.reindex e.symm) i)) = s ∘ e := by
    funext i
    simp only [Module.Basis.reindex_apply, Equiv.symm_symm, s, Function.comp_apply]
  have hg : Epi (L.freeHomEquiv.symm
      (bertiniSectionFamily L (fun i ↦ ψ ((b.reindex e.symm) i)))) := by
    rw [hsections]
    exact reindex_generating L e s hgen
  have hImm := reindex_immersion e f L s hgen
  have : IsImmersion (ProjectiveSpace.homOfGeneratingSections _ f L
      (bertiniSectionFamily L (fun i ↦ ψ ((b.reindex e.symm) i))) hg) := by
    simpa only [hsections] using hImm
  obtain ⟨U, hU, hgood⟩ := exists_open_smooth_finite_coordinates f L (Fintype.card I)
    (b.reindex e.symm) ψ _hlinear hg
  let R := coefficientReindex (k := k) e
  refine ⟨R.hom ⁻¹ᵁ U, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hU
    obtain ⟨y, hy⟩ := R.hom.homeomorph.surjective x
    refine ⟨y, ?_⟩
    change R.hom y ∈ U
    change R.hom y = x at hy
    rwa [hy]
  · intro K _ _ a ha
    have hrange : Set.range (bertiniCoefficientPoint (k := k) (a ∘ e)) ⊆ (U : Set _) := by
      rintro _ ⟨z, rfl⟩
      rw [← coefficientPoint_reindex e a]
      exact ha (Set.mem_range_self z)
    have h := hgood K (a ∘ e) hrange
    rw [hsections, memberSection_reindex] at h
    exact h

end

end AlgebraicGeometry
