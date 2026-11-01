/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.NativeReductionPullbackPaste
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerPullbackNormalizations
import all WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerDerivedPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat

/-! # Pasting the normalized scalar and geometric pullback comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open SheafOfModules
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]


set_option synthInstance.maxHeartbeats 200000 in
-- Resolve instances across the equivalent integral and section-module presentations.
set_option maxHeartbeats 1600000 in
-- Comparing the two localization models involves dependent module presentations.
private theorem pullComplexComparison_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (P : CochainComplex (Modules l E Z) ℤ) :
    (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) f g).hom.app
        (DerivedCategory.Q.obj P) ≫
      (pull l E f).map (pullComplexComparison l E g P).hom ≫
      (pullComplexComparison l E f
        (((CondensedRing.upperStar (spIntegralCondensed l E) g).mapHomologicalComplex
          (.up ℤ)).obj P)).hom =
    (pullComplexComparison l E (f ≫ g) P).hom ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (CondensedRing.upperStarComp (spIntegralCondensed l E) f g) (.up ℤ)).hom.app P) := by
  let pF := CondensedRing.upperStar (spIntegralCondensed l E) f
  let eF := pF.leftDerivedFunctorIsoMapDerivedCategory
  simp only [CondensedRing.leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, pullComplexComparison,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  simp only [Iso.inv_hom_id_app_assoc, pull,
    CondensedRing.moduleObjectDerivedPullback]
  rw [← eF.inv.naturality_assoc]
  rw [← eF.inv.naturality_assoc]
  dsimp only [eF, pF]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors
    (CondensedRing.upperStar (spIntegralCondensed l E) g)
    (CondensedRing.upperStar (spIntegralCondensed l E) f) P,
    Functor.mapDerivedCategoryNatIso_fac
      (CondensedRing.upperStarComp (spIntegralCondensed l E) f g) P]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Resolve instances across the equivalent integral and section-module presentations.
set_option maxHeartbeats 1600000 in
-- Transfer flatness through the internal-to-section module equivalence.
private theorem pullback_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules l E Y)
    (hM : IsFlatOnSite (J := Scheme.ProEt.topology Y)
      (R := spIntegralSectionRing l E Y)
      ((spIntegralModuleEquivalence l E Y).functor.obj M)) :
    IsFlatOnSite (J := Scheme.ProEt.topology X) (R := spIntegralSectionRing l E X)
      ((spIntegralModuleEquivalence l E X).functor.obj
        ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M)) := by
  apply (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology X) (condensedRingObj (spIntegralCondensed l E) X) _).mp
  apply Functor.PreservesFlat.flat_obj (F := CondensedRing.upperStar (spIntegralCondensed l E) f)
  exact (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology Y) (condensedRingObj (spIntegralCondensed l E) Y) M).mpr hM

private theorem exact_compositor_fac
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P) ≫
        (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj P) ≫
          H.mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  rw [Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P))).mp
  rw [Iso.hom_inv_id_app_assoc]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F G P]
  simp only [Category.assoc]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Resolve instances across the equivalent integral and section-module presentations.
set_option maxHeartbeats 2400000 in
-- This combines comparisons across three different module presentations.
/-- The pasted derived comparison has the representative equation of the pasted
ordinary comparison; no comparison for the composite is used in this calculation.
Source: normalized scalar/pullback construction, paragraphs (2)--(3).
Proof: geometric pullback preserves the flat-term K-flat resolving class. Apply
ReductionPull.representatives first for g on P, then for f on g-star P.
Naturality of the derived f comparison moves the canonical g representative
isomorphism across it. Naturality of the exact system factorization moves the
ordinary g comparison across it. The exact system compositor termwise formula
identifies its two factorization maps with that of the composite. The integral
left-derived compositor, followed by the two canonical representative comparisons,
is the localization of the ordinary integral compositor. Finally naturality of
the universal reduction counit moves this ordinary compositor across reduction.
Reassociate and use functoriality of localization to obtain the displayed equation.
This calculation uses only the comparisons for f and g, and makes no equality
claim between the ordinary pasted comparison and that for f followed by g.
(blueprint: lem-dla1-native-reduction-derived-pasting). -/
theorem nativeReductionDerivedPaste_normalized (s : Presentation l E)
    (q : ReductionGeometry l E s) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    DerivedPullNormalized l E s (f ≫ g) (nativeReductionOrdinaryPaste l E s q f g)
      (nativeReductionDerivedPaste l E s q f g) := by
  intro P hP hflat
  let pg := CondensedRing.upperStar (spIntegralCondensed l E) g
  let pf := CondensedRing.upperStar (spIntegralCondensed l E) f
  let rg := (s.operations.geometry g).pull
  let rf := (s.operations.geometry f).pull
  let rh := (s.operations.geometry (f ≫ g)).pull
  let R := derivedReduction l E s X
  let PG := (pg.mapHomologicalComplex (.up ℤ)).obj P
  let SZP := ((ordinaryReduction l E s Z).mapHomologicalComplex (.up ℤ)).obj P
  let a := (NatIso.mapHomologicalComplex
    (CondensedRing.upperStarComp (spIntegralCondensed l E) f g) (.up ℤ)).hom.app P
  let b := (NatIso.mapHomologicalComplex (q.pullback f).ordinary (.up ℤ)).hom.app PG
  let c := (NatIso.mapHomologicalComplex (q.pullback g).ordinary (.up ℤ)).hom.app P
  let k := (NatIso.mapHomologicalComplex (s.operations.ordinaryComp f g)
    (.up ℤ)).hom.app SZP
  have hg := (q.pullback g).representatives P hP hflat
  have hf := (q.pullback f).representatives PG
    (pullback_kflat l E g P hP) (fun i ↦ pullback_flat l E g (P.X i) (hflat i))
  have hc : (s.operations.comp f g).hom.app (DerivedCategory.Q.obj SZP) ≫
        rh.mapDerivedCategoryFactors.hom.app SZP =
      rf.mapDerivedCategory.map (rg.mapDerivedCategoryFactors.hom.app SZP) ≫
        rf.mapDerivedCategoryFactors.hom.app
          ((rg.mapHomologicalComplex (.up ℤ)).obj SZP) ≫ DerivedCategory.Q.map k := by
    rw [s.operations.comp_termwise]
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
      exact_compositor_fac rg rf rh (s.operations.ordinaryComp f g) SZP
  have hn := (reductionCounit l E s X).naturality a
  simp only [reductionCounit_app, Functor.comp_map] at hn
  have ho : (NatIso.mapHomologicalComplex
      (nativeReductionOrdinaryPaste l E s q f g) (.up ℤ)).hom.app P =
      ((ordinaryReduction l E s X).mapHomologicalComplex (.up ℤ)).map a ≫
        b ≫ (rf.mapHomologicalComplex (.up ℤ)).map c ≫ k := by
    ext i
    simp [nativeReductionOrdinaryPaste, a, b, c, k, PG, SZP, rf, pg,
      NatIso.mapHomologicalComplex, Functor.mapHomologicalComplex,
      Category.assoc]
  dsimp only [nativeReductionDerivedPaste, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.assoc,
    Functor.comp_map, pull, CondensedRing.moduleObjectDerivedPullback]
  rw [← (s.operations.comp f g).hom.naturality_assoc, hc]
  dsimp only [SpTowerShriek.pull, Functor.comp_map] at hg hf ⊢
  erw [← rf.mapDerivedCategory.map_comp_assoc, ← rf.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  rw [hg]
  change R.map _ ≫ _ = R.map _ ≫ _
  rw [rf.mapDerivedCategory.map_comp, rf.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  erw [← (q.pullback f).derived.hom.naturality_assoc]
  erw [rf.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [reassoc_of% hf]
  change R.map _ ≫ R.map _ ≫ R.map _ ≫ _ = R.map _ ≫ _
  rw [← R.map_comp_assoc, ← R.map_comp_assoc]
  simp only [Category.assoc]
  erw [pullComplexComparison_comp, R.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  rw [ho]
  simp only [Functor.map_comp]
  rfl

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
