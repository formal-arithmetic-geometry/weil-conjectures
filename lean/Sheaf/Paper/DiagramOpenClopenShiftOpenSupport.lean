/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Sheaf.Paper.DiagramOpenClopenShiftCore
import all Sheaf.Paper.DiagramOpenClopenShiftCore
import all Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import all Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.CategoryTheory.ExactDerivedAdjunctionUnitShift
import Sheaf.CategoryTheory.DerivedCategory.DerivedMateComparison
import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
import all Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import all Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift

/-! # Concrete open shift models on whole semilinear systems

Source: Stacks Project, Tags 03DI, 03DJ, 04TQ--04TS, 015F, 070H and 07A6;
blueprint `fix-prop-coherence`, maps-used sentence
(blueprint: lem-sf-diagram-open-model-construction).

The maps are the existing proper/open calculus maps. Representatives are natural
transformations of whole systems, localized through the standard factorizations.
The right-derived shift is the existing K-injective shift, rather than a shift
transported along a clopen isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a av aw b bv bw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private instance ordinaryOpenUnitIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] : IsIso (ordinaryOpenAdj C τ s).unit := by
  have : (VaryingRing.pull C τ s).IsRightAdjoint := VaryingRing.pull_isRightAdjoint C τ s
  exact chosen_unit_isIso_congr (pull C τ s) (VaryingRing.pull C τ s)
    (pull_eq C τ s) (VaryingRing.moduleJAdj_unit_isIso C τ s)

private def ordinaryComp {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    extension C τ s ⋙ extension C τ b ≅ extension C τ (s ≫ b) :=
  Adjunction.leftAdjointCompIso (ordinaryOpenAdj C τ s) (ordinaryOpenAdj C τ b)
    (ordinaryOpenAdj C τ (s ≫ b)) (pullComp C τ s b).symm

private def ordinaryRestriction {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    extension C τ (s ≫ b) ⋙ pull C τ b ≅ extension C τ s :=
  Functor.isoWhiskerRight (ordinaryComp C τ s b).symm (pull C τ b) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (extension C τ s) (asIso (ordinaryOpenAdj C τ b).unit).symm ≪≫
    Functor.rightUnitor _

private theorem ordinary_restriction_adjunct {U V X : Scheme.{u}}
    (s : U ⟶ V) (b : V ⟶ X) [IsOpenImmersion s] [IsOpenImmersion b]
    (N : Modules C τ U) :
    (ordinaryOpenAdj C τ s).homEquiv _ _ ((ordinaryRestriction C τ s b).inv.app N) =
      (ordinaryOpenAdj C τ (s ≫ b)).unit.app N ≫
        (pullComp C τ s b).hom.app ((extension C τ (s ≫ b)).obj N) := by
  simpa [ordinaryRestriction, ordinaryComp, Adjunction.homEquiv_unit,
    Category.assoc, Functor.map_comp] using
      openComp_unit (ordinaryOpenAdj C τ s) (ordinaryOpenAdj C τ b)
        (ordinaryOpenAdj C τ (s ≫ b)) (pullComp C τ s b) N

private theorem ordinary_compositor_zero {U V X T : Scheme.{u}}
    (s : U ⟶ V) (b : V ⟶ X) (t : T ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion t]
    (ht : Disjoint (Set.range t) (Set.range (s ≫ b))) (N : Modules C τ U) :
    (pull C τ t).map ((ordinaryComp C τ s b).hom.app N) = 0 := by
  have hz : IsZero ((pull C τ t).obj ((extension C τ (s ≫ b)).obj N)) := by
    rw [pull_eq, extension_eq]
    exact VaryingRing.disjoint_extension C τ (s ≫ b) t ht.symm N
  exact hz.eq_of_tgt _ _

private instance openAdjShift {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] : (jAdj C τ s).CommShift ℤ :=
  Adjunction.CommShift.mk' _ ℤ
    (Adjunction.mapExactDerivedCategory_unit_commShift (ordinaryOpenAdj C τ s)).2

private theorem pComp_shift {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X) :
    NatTrans.CommShift (pComp C τ s b).hom ℤ := by
  change NatTrans.CommShift
    ((Functor.mapDerivedCategoryNatIso (pullComp C τ s b)).hom ≫
      (Functor.mapDerivedCategoryCompIso (pull C τ b) (pull C τ s)).hom) ℤ
  infer_instance

private theorem jComp_shift {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    NatTrans.CommShift (jComp C τ s b).hom ℤ := by
  have := pComp_shift C τ s b
  exact leftAdjointComp_shift (jAdj C τ s) (jAdj C τ b)
    (jAdj C τ (s ≫ b)) (pComp C τ s b)

private theorem restriction_adjunct {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] (N : Derived C τ U) :
    (jAdj C τ s).homEquiv _ _ ((restrictionIso C τ s b).inv.app N) =
      (jAdj C τ (s ≫ b)).unit.app N ≫
        (pComp C τ s b).hom.app ((J C τ (s ≫ b)).obj N) := by
  have := jAdj_unit_isIso C τ b
  simpa [restrictionIso, Adjunction.homEquiv_unit, Category.assoc,
    Functor.map_comp, jComp] using
      openComp_unit (jAdj C τ s) (jAdj C τ b) (jAdj C τ (s ≫ b))
        (pComp C τ s b) N

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_inverse_localizes {U V X : Scheme.{u}}
    (s : U ⟶ V) (b : V ⟶ X) [IsOpenImmersion s] [IsOpenImmersion b]
    (K : CochainComplex (Modules C τ U) ℤ) :
    (restrictionIso C τ s b).inv.app (DerivedCategory.Q.obj K) ≫
      (pull C τ b).mapDerivedCategory.map
        ((extension C τ (s ≫ b)).mapDerivedCategoryFactors.hom.app K) ≫
      (pull C τ b).mapDerivedCategoryFactors.hom.app
        (((extension C τ (s ≫ b)).mapHomologicalComplex (.up ℤ)).obj K) =
    (extension C τ s).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (ordinaryRestriction C τ s b).inv (.up ℤ)).app K) := by
  exact exact_restriction_localizes (pull C τ b)
    (ordinaryOpenAdj C τ (s ≫ b)) (ordinaryOpenAdj C τ s) (pullComp C τ s b)
    (ordinaryRestriction C τ s b).inv (ordinary_restriction_adjunct C τ s b)
    (restrictionIso C τ s b).inv (restriction_adjunct C τ s b) K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def restrictionModel {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    TermwiseModel (extension C τ (s ≫ b) ⋙ pull C τ b) (extension C τ s)
      ((Functor.mapDerivedCategoryCompIso _ _).hom ≫ (restrictionIso C τ s b).hom) :=
  termwiseMapModel ((ordinaryRestriction C τ s b).hom) _ (by
    intro K
    dsimp only [NatTrans.comp_app]
    rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors
      (extension C τ (s ≫ b)) (pull C τ b) K]
    simp only [Category.assoc]
    congr 1
    apply (cancel_epi ((restrictionIso C τ s b).inv.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.inv_hom_id_app_assoc]
    have hi0 := restriction_inverse_localizes C τ s b K
    rw [← Category.assoc] at hi0
    erw [reassoc_of% hi0]
    rw [← Functor.map_comp]
    have hi : (NatTrans.mapHomologicalComplex (ordinaryRestriction C τ s b).inv
        (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex (ordinaryRestriction C τ s b).hom (.up ℤ)).app K =
        𝟙 _ := (NatIso.mapHomologicalComplex (ordinaryRestriction C τ s b) (.up ℤ)).inv_hom_id_app K
    rw [hi, DerivedCategory.Q.map_id, Category.comp_id]
  )

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def compositorModel {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    TermwiseModel (extension C τ s ⋙ extension C τ b) (extension C τ (s ≫ b))
      ((Functor.mapDerivedCategoryCompIso _ _).hom ≫ (jComp C τ s b).hom) :=
  termwiseMapModel ((ordinaryComp C τ s b).hom) _ (by
    intro K
    simpa only [NatTrans.comp_app, Category.assoc, jComp, jAdj,
      SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction, ordinaryComp, pComp]
      using exact_compositor_localizes (ordinaryOpenAdj C τ s)
        (ordinaryOpenAdj C τ b) (ordinaryOpenAdj C τ (s ≫ b)) (pullComp C τ s b) K
  )

private theorem restriction_shift {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    NatTrans.CommShift (restrictionIso C τ s b).hom ℤ := by
  have := jComp_shift C τ s b
  have := NatTrans.CommShift.of_iso_inv (jComp C τ s b) ℤ
  have := jAdj_unit_isIso C τ b
  have : NatTrans.CommShift (asIso (jAdj C τ b).unit).hom ℤ := by
    change NatTrans.CommShift (jAdj C τ b).unit ℤ
    infer_instance
  have : NatTrans.CommShift (asIso (jAdj C τ b).unit).inv ℤ :=
    NatTrans.CommShift.of_iso_inv (asIso (jAdj C τ b).unit) ℤ
  dsimp only [restrictionIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance

private theorem restriction_identity {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] (N : Derived C τ U) :
    (jAdj C τ (s ≫ b)).unit.app N ≫
      (pComp C τ s b).hom.app ((J C τ (s ≫ b)).obj N) ≫
      (P C τ s).map ((restrictionIso C τ s b).hom.app N) =
        (jAdj C τ s).unit.app N := by
  rw [← Category.assoc, ← restriction_adjunct C τ s b N, Adjunction.homEquiv_unit]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp

private def ordinaryToDirect {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] :
    extension C τ s ⟶ push C τ s :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (extension C τ s) (ordinaryAdj C τ s).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inv (ordinaryOpenAdj C τ s).unit) (push C τ s) ≫
    (Functor.leftUnitor _).hom

private theorem ordinaryToDirect_app {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] (N : Modules C τ U) :
    (ordinaryToDirect C τ s).app N =
      (ordinaryAdj C τ s).unit.app ((extension C τ s).obj N) ≫
        (push C τ s).map ((inv (ordinaryOpenAdj C τ s).unit).app N) := by
  simp [ordinaryToDirect]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryToDirect_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : IsIso (ordinaryToDirect C τ s) := by
  obtain ⟨e⟩ := VaryingRing.ordinary_clopen_iso C τ s
  have he : Nonempty (extension C τ s ≅ push C τ s) := by
    rw [extension_eq, push_eq]
    exact ⟨e⟩
  obtain ⟨e⟩ := he
  let ff := (ordinaryOpenAdj C τ s).fullyFaithfulLOfIsIsoUnit
  let fp := ff.ofIso e
  have := fp.full
  have := fp.faithful
  have hi (N : Modules C τ U) : IsIso ((ordinaryToDirect C τ s).app N) := by
    have : IsIso ((ordinaryAdj C τ s).unit.app ((extension C τ s).obj N)) :=
      (ordinaryAdj C τ s).isIso_unit_app_of_iso (e.app N)
    rw [ordinaryToDirect_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private def ordinaryDirect {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : extension C τ s ≅ push C τ s :=
  @asIso _ _ _ _ (ordinaryToDirect C τ s) (ordinaryToDirect_isIso C τ s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryDirect_adjunct {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (N : Modules C τ U) :
    ((ordinaryAdj C τ s).homEquiv _ _).symm ((ordinaryDirect C τ s).hom.app N) ≫
      (ordinaryOpenAdj C τ s).unit.app N = 𝟙 _ := by
  have he : ((ordinaryAdj C τ s).homEquiv _ _).symm
      ((ordinaryDirect C τ s).hom.app N) = (inv (ordinaryOpenAdj C τ s).unit).app N := by
    apply ((ordinaryAdj C τ s).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact ordinaryToDirect_app C τ s N
  rw [he, ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem direct_localized {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    [PreservesFiniteColimits (push C τ s)] :
    openToS C τ s ≫ (push C τ s).rightDerivedFunctorIsoMapDerivedCategory.hom =
      (Functor.mapDerivedCategoryNatIso (ordinaryDirect C τ s)).hom := by
  have hjiso : IsIso (jAdj C τ s).unit := jAdj_unit_isIso C τ s
  have hj : jAdj C τ s = VaryingRing.exactAdj (ordinaryOpenAdj C τ s) :=
    exactAdj_eq (ordinaryOpenAdj C τ s)
  have hu := VaryingRing.exactAdj_isoUnit (ordinaryOpenAdj C τ s)
  rw [← hj] at hu
  have hi : inv (jAdj C τ s).unit =
      ((Functor.mapDerivedCategoryCompIso (extension C τ s) (pull C τ s)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (asIso (ordinaryOpenAdj C τ s).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso (Modules C τ U)).hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hu]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact (Functor.mapDerivedCategoryIdIso _).inv_hom_id
  ext N
  have ht := VaryingRing.localizedTranspose (ordinaryAdj C τ s)
    (ordinaryDirect C τ s) (asIso (ordinaryOpenAdj C τ s).unit).symm
    (fun M ↦ (ordinaryToDirect_app C τ s M).symm) N
  rw [← hi] at ht
  have he := congr_app (congrArg Adjunction.unit
    (VaryingRing.exactAdj_eq_rightDerived (ordinaryAdj C τ s))) ((J C τ s).obj N)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at he
  have hn := (push C τ s).rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((inv (jAdj C τ s).unit).app N)
  simp only [NatTrans.comp_app, openToS, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp]
  dsimp only [P, J, R, Functor.id_obj, Functor.comp_obj] at hn he ht ⊢
  simp only [Category.comp_id, Category.assoc]
  change (adj C τ s).unit.app ((J C τ s).obj N) ≫
    (push C τ s).rightDerivedFunctor.map ((inv (jAdj C τ s).unit).app N) ≫ _ = _
  rw [hn, ← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ (push C τ s).mapDerivedCategory.map
    ((inv (jAdj C τ s).unit).app N)) he).trans ht

private def ordinaryPi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Modules C τ X) ⟶ pull C τ s ⋙ extension C τ s :=
  (ordinaryAdj C τ s).unit ≫
    Functor.whiskerLeft (pull C τ s) (ordinaryDirect C τ s).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryPi_unit {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    ordinaryPi C τ s ≫ Functor.whiskerLeft (pull C τ s) (ordinaryDirect C τ s).hom =
      (ordinaryAdj C τ s).unit := by
  simp [ordinaryPi, Category.assoc, ← Functor.whiskerLeft_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryPi_component {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Modules C τ X) :
    (pull C τ s).map ((ordinaryPi C τ s).app M) =
      (ordinaryOpenAdj C τ s).unit.app ((pull C τ s).obj M) := by
  let t : Adjunction.Triple (extension C τ s) (pull C τ s) (push C τ s) :=
    ⟨ordinaryOpenAdj C τ s, ordinaryAdj C τ s⟩
  let ff := (ordinaryOpenAdj C τ s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let fp := ff.ofIso (ordinaryDirect C τ s)
  have := fp.full
  have := fp.faithful
  have he : (ordinaryDirect C τ s).hom = t.leftToRight := by
    ext N
    simp [ordinaryDirect, ordinaryToDirect, t, Adjunction.Triple.leftToRight]
  simp only [ordinaryPi, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Functor.map_comp]
  apply (cancel_mono ((pull C τ s).map
    ((ordinaryDirect C τ s).hom.app ((pull C τ s).obj M)))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [he, t.leftToRight_app_obj]
  dsimp only [t]
  simp only [Functor.map_comp]
  change _ = (ordinaryOpenAdj C τ s).unit.app _ ≫
    (pull C τ s).map ((ordinaryOpenAdj C τ s).counit.app M) ≫ _
  rw [← Category.assoc, (ordinaryOpenAdj C τ s).right_triangle_components]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private def localizedPi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Derived C τ X) ⟶ P C τ s ⋙ J C τ s :=
  (Functor.mapDerivedCategoryIdIso _).inv ≫
    VaryingRing.derivedMap (ordinaryPi C τ s) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem id_factors {X : Scheme.{u}} (K : CochainComplex (Modules C τ X) ℤ) :
    (Functor.mapDerivedCategoryIdIso (Modules C τ X)).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 (Modules C τ X)).mapDerivedCategoryFactors.hom.app K := by
  have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj
    (Modules C τ X) ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  erw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  have hq (L : CochainComplex (Modules C τ X) ℤ) :
      (DerivedCategory.quotientCompQhIso (Modules C τ X)).hom.app L = 𝟙 _ :=
    Quotient.lift.isLift_hom _ _ _ L
  have hqi (L : CochainComplex (Modules C τ X) ℤ) :
      (DerivedCategory.quotientCompQhIso (Modules C τ X)).inv.app L = 𝟙 _ :=
    Quotient.lift.isLift_inv _ _ _ L
  rw [hq, hqi] at h
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp, DerivedCategory.Qh.map_id,
    Category.comp_id] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localizedPi_fac {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (K : CochainComplex (Modules C τ X) ℤ) :
    (localizedPi C τ s).app (DerivedCategory.Q.obj K) ≫
      (J C τ s).map ((pull C τ s).mapDerivedCategoryFactors.hom.app K) ≫
      (extension C τ s).mapDerivedCategoryFactors.hom.app
        (((pull C τ s).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinaryPi C τ s)
        (.up ℤ)).app K) := by
  exact localized_id_map_fac (ordinaryPi C τ s) K (id_factors C τ K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localizedPi_toDirect {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    [PreservesFiniteColimits (push C τ s)] :
    localizedPi C τ s ≫ Functor.whiskerLeft (P C τ s) (openToS C τ s) =
      (adj C τ s).unit := by
  let e := (push C τ s).rightDerivedFunctorIsoMapDerivedCategory
  apply (cancel_mono (Functor.whiskerLeft (P C τ s) e.hom)).mp
  have he := congrArg Adjunction.unit
    (VaryingRing.exactAdj_eq_rightDerived (ordinaryAdj C τ s))
  change (adj C τ s).unit ≫ Functor.whiskerLeft (P C τ s) e.hom =
    (VaryingRing.exactAdj (ordinaryAdj C τ s)).unit at he
  rw [Category.assoc, ← Functor.whiskerLeft_comp, direct_localized, he]
  rw [← exactAdj_eq]
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules C τ X) (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_mono ((push C τ s).mapDerivedCategory.map
      ((pull C τ s).mapDerivedCategoryFactors.hom.app K) ≫
    (push C τ s).mapDerivedCategoryFactors.hom.app
      (((pull C τ s).mapHomologicalComplex (.up ℤ)).obj K))).mp
  have hn := (Functor.mapDerivedCategoryNatIso (ordinaryDirect C τ s)).hom.naturality
    ((pull C τ s).mapDerivedCategoryFactors.hom.app K)
  erw [Category.assoc, ← reassoc_of% hn, Functor.mapDerivedCategoryNatIso_fac]
  erw [reassoc_of% (localizedPi_fac C τ s K), exact_unit_fac, ← DerivedCategory.Q.map_comp]
  congr 1
  ext p : 1
  exact congr_app (ordinaryPi_unit C τ s) (K.X p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localizedPi_eq {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    [PreservesFiniteColimits (push C τ s)] : localizedPi C τ s = pi C τ s := by
  have := openToS_isIso C τ s
  apply (cancel_mono (Functor.whiskerLeft (P C τ s) (openToS C τ s))).mp
  rw [localizedPi_toDirect]
  simp [pi, Category.assoc, ← Functor.whiskerLeft_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def projectionModel {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    [PreservesFiniteColimits (push C τ s)] :
    TermwiseModel (𝟭 (Modules C τ X)) (pull C τ s ⋙ extension C τ s)
      ((Functor.mapDerivedCategoryIdIso _).hom ≫ pi C τ s ≫
        (Functor.mapDerivedCategoryCompIso _ _).inv) :=
  termwiseMapModel (ordinaryPi C τ s) _ (by
    intro K
    rw [← localizedPi_eq]
    dsimp only [localizedPi]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id]
    exact VaryingRing.derivedMap_fac (ordinaryPi C τ s) K
  )

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openToS_shift {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] : NatTrans.CommShift (openToS C τ s) ℤ := by
  have ha : (adj C τ s).CommShift ℤ :=
    canonicalRightDerivedAdjunctionShift (ordinaryAdj C τ s)
  have := jAdj_unit_isIso C τ s
  have hi : NatTrans.CommShift (asIso (jAdj C τ s).unit).hom ℤ := by
    change NatTrans.CommShift (jAdj C τ s).unit ℤ
    infer_instance
  have hui : NatTrans.CommShift (inv (jAdj C τ s).unit) ℤ :=
    NatTrans.CommShift.of_iso_inv (asIso (jAdj C τ s).unit) ℤ
  have hau : NatTrans.CommShift (adj C τ s).unit ℤ := inferInstance
  dsimp only [openToS]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pi_shift {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : NatTrans.CommShift (pi C τ s) ℤ := by
  have ha : (adj C τ s).CommShift ℤ :=
    canonicalRightDerivedAdjunctionShift (ordinaryAdj C τ s)
  have := openToS_shift C τ s
  have := openToS_isIso C τ s
  have hi : NatTrans.CommShift (asIso (openToS C τ s)).hom ℤ := by
    change NatTrans.CommShift (openToS C τ s) ℤ
    infer_instance
  have hti : NatTrans.CommShift (inv (openToS C τ s)) ℤ :=
    NatTrans.CommShift.of_iso_inv (asIso (openToS C τ s)) ℤ
  have hau : NatTrans.CommShift (adj C τ s).unit ℤ := inferInstance
  dsimp only [pi]
  infer_instance

section UnitCoherence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.catToReflQuiver in
private def ordinaryPushId (X : Scheme.{u}) : push C τ (𝟙 X) ≅ 𝟭 (Modules C τ X) :=
  (pushId_existsUnique C τ X).choose

attribute [-instance] CategoryTheory.catToReflQuiver in
private def ordinaryPullId (X : Scheme.{u}) : pull C τ (𝟙 X) ≅ 𝟭 (Modules C τ X) :=
  Adjunction.leftAdjointIdIso (ordinaryAdj C τ (𝟙 X)) (ordinaryPushId C τ X)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem push_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushComp C τ (𝟙 X) f ≪≫ eqToIso (congrArg (push C τ) (Category.id_comp f)) =
      Functor.isoWhiskerRight (ordinaryPushId C τ X) (push C τ f) ≪≫
        Functor.leftUnitor (push C τ f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  cases V using Opposite.rec
  rename_i V
  rcases V with ⟨n, V⟩
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [push_map_apply C τ f ((ordinaryPushId C τ X).hom.app M) n V]
  erw [(pushId_existsUnique C τ X).choose_spec.1 M n
    ((Scheme.proEtaleBaseChange f).obj V)]
  erw [push_transport C τ (Category.id_comp f) M n V]
  erw [pushComp_apply C τ (𝟙 X) f M n V]
  rw [← PresheafOfModules.map_comp_apply, ← CategoryTheory.op_comp]
  apply StrictTower.restriction_eq M.val
  change Prod.mkHom (𝟙 n) _ ≫ Prod.mkHom (𝟙 n) _ = Prod.mkHom (𝟙 n) _
  rw [prod_comp, Category.id_comp]
  exact congrArg (Prod.mkHom (𝟙 n))
    (StrictTower.site_left_unit (P := @WeaklyEtale.{u}) (Q := ⊤) f V)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    eqToIso (congrArg (pull C τ) (Category.id_comp f).symm) ≪≫
      pullComp C τ (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (pull C τ f) (ordinaryPullId C τ X) ≪≫
      Functor.rightUnitor (pull C τ f) = Iso.refl _ := by
  have h := Adjunction.leftAdjointCompIso_comp_id (ordinaryAdj C τ f)
    (ordinaryAdj C τ (𝟙 X))
    (pushComp C τ (𝟙 X) f ≪≫ eqToIso (congrArg (push C τ) (Category.id_comp f)))
    (ordinaryPushId C τ X) (push_left_unit C τ f)
  rw [StrictTower.mate_transport (pull C τ) (push C τ) (fun t ↦ ordinaryAdj C τ t)
    (ordinaryAdj C τ f) (ordinaryAdj C τ (𝟙 X)) (Category.id_comp f)
    (pushComp C τ (𝟙 X) f)] at h
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hi := congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at hi
  change (eqToIso (congrArg (pull C τ) (Category.id_comp f).symm)).hom.app M ≫
    (pullComp C τ (𝟙 X) f).hom.app M =
      𝟙 _ ≫ (ordinaryPullId C τ X).inv.app ((pull C τ f).obj M) at hi
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id]
  rw [← Category.assoc, hi]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem inverse_image_left_unit {U X : Scheme.{u}} (s : U ⟶ X)
    (M : Derived C τ X) :
    (pComp C τ (𝟙 U) s).inv.app M ≫
      (eqToIso (congrArg (P C τ) (Category.id_comp s))).hom.app M =
        (pId C τ U).hom.app ((P C τ s).obj M) := by
  have hh := StrictTower.descend_left_unit (pull C τ s) (pull C τ (𝟙 U ≫ s))
    (pull C τ (𝟙 U)) (eqToIso (congrArg (pull C τ) (Category.id_comp s).symm))
    (pullComp C τ (𝟙 U) s) (ordinaryPullId C τ U) (ordinary_left_unit C τ s)
  rw [pull_derived_transport C τ (Category.id_comp s).symm] at hh
  have h := congr_app hh M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at h
  have h' : (eqToIso (congrArg (P C τ) (Category.id_comp s).symm)).hom.app M ≫
      (pComp C τ (𝟙 U) s).hom.app M ≫
        (pId C τ U).hom.app ((P C τ s).obj M) = 𝟙 _ := by
    simpa only [pComp, pId, ordinaryPullId, ordinaryPushId, P, Iso.trans_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using h
  have hk := (Iso.hom_comp_eq_id
    ((eqToIso (congrArg (P C τ) (Category.id_comp s).symm)).app M)).1 h'
  dsimp only [Iso.app_inv] at hk
  change (pComp C τ (𝟙 U) s).inv.app M ≫
    (eqToIso (congrArg (P C τ) (Category.id_comp s).symm)).inv.app M = _
  rw [← hk, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem push_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushComp C τ f (𝟙 Y) ≪≫ eqToIso (congrArg (push C τ) (Category.comp_id f)) =
      Functor.isoWhiskerLeft (push C τ f) (ordinaryPushId C τ Y) ≪≫
        Functor.rightUnitor (push C τ f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  cases V using Opposite.rec
  rename_i V
  rcases V with ⟨n, V⟩
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [(pushId_existsUnique C τ Y).choose_spec.1 ((push C τ f).obj M) n V]
  erw [push_obj_map_apply C τ f M n
    ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ Y).inv.app V)]
  erw [push_transport C τ (Category.comp_id f) M n V]
  erw [pushComp_apply C τ f (𝟙 Y) M n V]
  rw [← PresheafOfModules.map_comp_apply, ← CategoryTheory.op_comp]
  apply StrictTower.restriction_eq M.val
  change Prod.mkHom (𝟙 n) _ ≫ Prod.mkHom (𝟙 n) _ = Prod.mkHom (𝟙 n) _
  rw [prod_comp, Category.id_comp]
  exact congrArg (Prod.mkHom (𝟙 n))
    (StrictTower.site_right_unit (P := @WeaklyEtale.{u}) (Q := ⊤) f V)


attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    eqToIso (congrArg (pull C τ) (Category.comp_id f).symm) ≪≫
      pullComp C τ f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (ordinaryPullId C τ Y) (pull C τ f) ≪≫
      Functor.leftUnitor (pull C τ f) = Iso.refl _ := by
  have h := Adjunction.leftAdjointCompIso_id_comp (ordinaryAdj C τ (𝟙 Y))
    (ordinaryAdj C τ f)
    (pushComp C τ f (𝟙 Y) ≪≫ eqToIso (congrArg (push C τ) (Category.comp_id f)))
    (ordinaryPushId C τ Y) (push_right_unit C τ f)
  rw [StrictTower.mate_transport (pull C τ) (push C τ) (fun t ↦ ordinaryAdj C τ t)
    (ordinaryAdj C τ (𝟙 Y)) (ordinaryAdj C τ f) (Category.comp_id f)
    (pushComp C τ f (𝟙 Y))] at h
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hi := congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at hi
  change (eqToIso (congrArg (pull C τ) (Category.comp_id f).symm)).hom.app M ≫
    (pullComp C τ f (𝟙 Y)).hom.app M =
      𝟙 _ ≫ (pull C τ f).map ((ordinaryPullId C τ Y).inv.app M) at hi
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.refl_hom, NatTrans.id_app]
  change ((eqToIso (congrArg (pull C τ) (Category.comp_id f).symm)).hom.app M ≫
    (pullComp C τ f (𝟙 Y)).hom.app M) ≫
      (pull C τ f).map ((ordinaryPullId C τ Y).hom.app M) = 𝟙 _
  rw [hi]
  simp [← Functor.map_comp]


attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem inverse_image_right_unit {U X : Scheme.{u}} (s : U ⟶ X)
    (M : Derived C τ X) :
    (pComp C τ s (𝟙 X)).inv.app M ≫
      (eqToIso (congrArg (P C τ) (Category.comp_id s))).hom.app M =
        (P C τ s).map ((pId C τ X).hom.app M) := by
  have hh := StrictTower.descend_right_unit (pull C τ s) (pull C τ (s ≫ 𝟙 X))
    (pull C τ (𝟙 X)) (eqToIso (congrArg (pull C τ) (Category.comp_id s).symm))
    (pullComp C τ s (𝟙 X)) (ordinaryPullId C τ X) (ordinary_right_unit C τ s)
  rw [pull_derived_transport C τ (Category.comp_id s).symm] at hh
  have h := congr_app hh M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at h
  have h' : (eqToIso (congrArg (P C τ) (Category.comp_id s).symm)).hom.app M ≫
      (pComp C τ s (𝟙 X)).hom.app M ≫
        (P C τ s).map ((pId C τ X).hom.app M) = 𝟙 _ := by
    simpa only [pComp, pId, ordinaryPullId, ordinaryPushId, P, Iso.trans_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc] using h
  have hk := (Iso.hom_comp_eq_id
    ((eqToIso (congrArg (P C τ) (Category.comp_id s).symm)).app M)).1 h'
  dsimp only [Iso.app_inv] at hk
  change (pComp C τ s (𝟙 X)).inv.app M ≫
    (eqToIso (congrArg (P C τ) (Category.comp_id s).symm)).inv.app M = _
  rw [← hk, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]


end UnitCoherence

private theorem extension_left_unit {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] (M : Derived C τ U) :
    (jComp C τ (𝟙 U) s).hom.app M ≫
      (jCongr C τ (Category.id_comp s)).hom.app M =
        (J C τ s).map ((jId C τ U).hom.app M) := by
  let e := (pComp C τ (𝟙 U) s).symm ≪≫
    eqToIso (congrArg (P C τ) (Category.id_comp s))
  have he : e = Functor.isoWhiskerLeft (P C τ s) (pId C τ U) ≪≫
      Functor.rightUnitor (P C τ s) := by
    apply Iso.ext
    ext N
    simpa [e] using inverse_image_left_unit C τ s N
  have h := Adjunction.leftAdjointCompIso_id_comp
    (jAdj C τ (𝟙 U)) (jAdj C τ s) e (pId C τ U) he
  rw [jComp_transport] at h
  simpa [jId] using congr_app (congrArg Iso.hom h) M

private theorem extension_right_unit {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] (M : Derived C τ U) :
    (jComp C τ s (𝟙 X)).hom.app M ≫
      (jCongr C τ (Category.comp_id s)).hom.app M =
        (jId C τ X).hom.app ((J C τ s).obj M) := by
  let e := (pComp C τ s (𝟙 X)).symm ≪≫
    eqToIso (congrArg (P C τ) (Category.comp_id s))
  have he : e = Functor.isoWhiskerRight (pId C τ X) (P C τ s) ≪≫
      Functor.leftUnitor (P C τ s) := by
    apply Iso.ext
    ext N
    simpa [e] using inverse_image_right_unit C τ s N
  have h := Adjunction.leftAdjointCompIso_comp_id
    (jAdj C τ s) (jAdj C τ (𝟙 X)) e (pId C τ X) he
  rw [jComp_transport] at h
  simpa [jId] using congr_app (congrArg Iso.hom h) M

/-- The canonical compositor and normalized open restriction, with their termwise
models, adjunct identities and shift squares. Source: Stacks 03DJ, 015F and 07A6;
blueprint maps-used argument (blueprint: lem-sf-diagram-open-model-construction).
Proof: construct the original open-model structure literal from the actual
ordinary comparison maps and their proved exact-localization equations. -/
theorem openModels_nonempty {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] : Nonempty (OpenModels C τ s b) := by
  exact ⟨{
    compositor := compositorModel C τ s b
    compositor_normalization := rfl
    ordinary_compositor_identity := openComp_unit (ordinaryOpenAdj C τ s)
      (ordinaryOpenAdj C τ b) (ordinaryOpenAdj C τ (s ≫ b)) (pullComp C τ s b)
    compositor_identity := openComp_unit (jAdj C τ s) (jAdj C τ b)
      (jAdj C τ (s ≫ b)) (pComp C τ s b)
    ordinaryRestriction := ordinaryRestriction C τ s b
    restriction := restrictionModel C τ s b
    restriction_ordinary := rfl
    ordinary_adjunct := ordinary_restriction_adjunct C τ s b
    derived_adjunct := restriction_adjunct C τ s b
    restriction_identity := restriction_identity C τ s b
    compositor_zero := fun t _ ht N ↦ ordinary_compositor_zero C τ s b t ht N
    compositor_shift := jComp_shift C τ s b
    restriction_shift := restriction_shift C τ s b }⟩

end AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift
