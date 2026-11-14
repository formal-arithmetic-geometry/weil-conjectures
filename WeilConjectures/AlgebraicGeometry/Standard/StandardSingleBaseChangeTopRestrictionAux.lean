/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.Derived.DerivedBaseChangeSourceTransport
import WeilConjectures.AlgebraicGeometry.Open.OpenSingleCoefficientTransport

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The derived pullback unit for a scheme isomorphism is invertible.
Source: Stacks Project, Tag 0D5S. -/
theorem standardSingleBaseChange_topRestriction_iso_pullback_unit
    [∀ X : Scheme.{u},
      HasDerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Z : Scheme.{u}} (s : X ≅ Z) :
    IsIso (relativeMVAdj s.hom).unit := by
  obtain ⟨_, i, _, _, _⟩ := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))
  let b : derivedPullback s.hom ⋙ derivedPullback s.inv ≅ 𝟭 _ :=
    relativeMVComp s.inv s.hom ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) s.inv_hom_id) ≪≫ i Z
  let c : derivedPullback s.inv ⋙ derivedPullback s.hom ≅ 𝟭 _ :=
    relativeMVComp s.hom s.inv ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) s.hom_inv_id) ≪≫ i X
  have : (derivedPullback s.inv).Faithful := Functor.Faithful.of_comp_iso c
  have : (derivedPullback s.hom).Faithful := Functor.Faithful.of_comp_iso b
  have : (derivedPullback s.hom).Full := Functor.Full.of_comp_faithful_iso b
  infer_instance

set_option linter.unusedVariables false in
/-- Canonical source restriction comparison for the top open.
Source: Stacks Project, Tags 08HY and 0D5S. -/
noncomputable def standardSingleBaseChange_topRestriction_sourceIso
    {Y B : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι)) := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let j := (⊤ : Y.Opens).ι
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  have : IsIso (relativeMVAdj j).unit :=
    standardSingleBaseChange_topRestriction_iso_pullback_unit Y.topIso
  let a : (derivedPullback j).obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj (M.restrict j) :=
    (singleComplexOpenPullbackIso Y ⊤).app K ≪≫
      ((schemeOpenRestriction Y ⊤).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings
          (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).mapIso
        ((Scheme.Modules.overFunctorEquiv ⊤).app M)
  exact (schemeDerivedDirectImage p).mapIso
      (asIso ((relativeMVAdj j).unit.app K)) ≪≫
    (relativeMVImageComp j p).app ((derivedPullback j).obj K) ≪≫
    (schemeDerivedDirectImage (j ≫ p)).mapIso a

set_option linter.unusedVariables false in
/-- Compatibility equation for the canonical source restriction comparison.
Source: Stacks Project, Tags 08HY and 0D5S. -/
theorem standardSingleBaseChange_topRestriction_compatibility
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∀ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι))),
      e = standardSingleBaseChange_topRestriction_sourceIso p M → ∃ (t : (schemeDerivedDirectImage
          (pullback.snd ((⊤ : Y.Opens).ι ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj
              (pullback.fst ((⊤ : Y.Opens).ι ≫ p) g)
              (M.restrict (⊤ : Y.Opens).ι))) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap ((⊤ : Y.Opens).ι ≫ p)
            (M.restrict (⊤ : Y.Opens).ι) g ≫ t.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  intro e he
  subst e
  let j := (⊤ : Y.Opens).ι
  let N := M.restrict j
  let r := pullback.fst p g
  let s := pullback.snd p g
  let r' := pullback.fst (j ≫ p) g
  let s' := pullback.snd (j ≫ p) g
  have h : r ≫ p = s ≫ g := pullback.condition
  have h' : r' ≫ (j ≫ p) = s' ≫ g := pullback.condition
  let kh : pullback (j ≫ p) g ⟶ pullback p g :=
    pullback.lift (r' ≫ j) s' (by simpa only [Category.assoc] using h')
  let ki : pullback p g ⟶ pullback (j ≫ p) g :=
    pullback.lift (r ≫ Y.topIso.inv) s (by
      change r ≫ Y.topIso.inv ≫ Y.topIso.hom ≫ p = s ≫ g
      simpa only [Iso.inv_hom_id_assoc] using h)
  let k : pullback (j ≫ p) g ≅ pullback p g :=
    { hom := kh
      inv := ki
      hom_inv_id := by
        apply pullback.hom_ext <;>
          simp [kh, ki, r, s, r', s', j, Category.assoc]
      inv_hom_id := by
        apply pullback.hom_ext <;>
          simp [kh, ki, r, s, r', s', j, Category.assoc] }
  have hr : k.hom ≫ r = r' ≫ j := pullback.lift_fst _ _ _
  have hs : k.hom ≫ s = s' := pullback.lift_snd _ _ _
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  let K' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).obj N
  let T := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj r M)
  let T' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback (j ≫ p) g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj r' N)
  let a : (derivedPullback j).obj K ≅ K' :=
    (singleComplexOpenPullbackIso Y ⊤).app K ≪≫
      ((schemeOpenRestriction Y ⊤).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings
          (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).mapIso
        ((Scheme.Modules.overFunctorEquiv ⊤).app M)
  obtain ⟨d, hd⟩ := exists_openSingle_coefficient_transport ⊤ M r r' k hr
  have : IsIso (relativeMVAdj k.hom).unit :=
    standardSingleBaseChange_topRestriction_iso_pullback_unit k
  let F : (schemeDerivedDirectImage s).obj T ≅
      (schemeDerivedDirectImage s').obj T' :=
    (schemeDerivedDirectImage s).mapIso (asIso ((relativeMVAdj k.hom).unit.app T)) ≪≫
      (relativeMVImageComp k.hom s).app ((derivedPullback k.hom).obj T) ≪≫
      eqToIso (congrArg (fun f ↦ (schemeDerivedDirectImage f).obj
        ((derivedPullback k.hom).obj T)) hs) ≪≫
      (schemeDerivedDirectImage s').mapIso d
  refine ⟨F.symm, ?_⟩
  have hc := derivedBaseChange_source_transport p g j r s r' s' k.hom h h' hr hs
    K K' T T' a.hom (Scheme.picardTermwiseSingleMap r M)
      (Scheme.picardTermwiseSingleMap r' N) d.hom hd
  have hc' : standardSingleBaseChangeMap p M g ≫ F.hom =
      (derivedPullback g).map
        (standardSingleBaseChange_topRestriction_sourceIso p M).hom ≫
          standardSingleBaseChangeMap (j ≫ p) N g := by
    simpa only [standardSingleBaseChangeMap,
      standardSingleBaseChange_topRestriction_sourceIso, F, a, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, asIso_hom, eqToIso.hom, Category.assoc] using hc
  have hh := congrArg (fun f ↦ f ≫ F.inv) hc'
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.symm_hom] using hh

end AlgebraicGeometry
