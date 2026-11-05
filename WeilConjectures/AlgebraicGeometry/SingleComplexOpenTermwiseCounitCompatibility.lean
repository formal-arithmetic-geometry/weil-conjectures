/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
import all WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTensorComparisonCoherence
import all WeilConjectures.AlgebraicGeometry.OpenPinnedTensorCounitTransport
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Compatibility of open restriction with the pinned pullback counits

Source: Stacks Project, cohomology.tex, Tags 08HY, 08FE and 0D5S.
(blueprint: lem-pc-single-complex-open-counit-compatibility).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange
set_option synthInstance.maxSize 2048

section CounitRestriction

private noncomputable def termwise_openPinnedHomotopyTensorRestrictionIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) :
    (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
        (schemeOpenRestriction X' U').mapHomotopyCategory (.up ℤ) ≅
      (schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ) :=
  by
    dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
    letI := schemeOpenRestriction_additive X U
    letI := schemeOpenRestriction_additive X' U'
    exact Functor.mapHomotopyCategoryCompIso (openPinnedTensorRestrictionIso k U U' j hj) (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j)) (.up ℤ)).symm

private theorem termwise_targetHomotopyComparison
    {C D E : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] [Preadditive E]
    {F : C ⥤ D} {G R : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [R.Additive] [H.Additive]
    (e : G ≅ R) (a : F ⋙ G ≅ H) (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).hom.app P ≫
        (Functor.mapHomotopyCategoryCompIso
          (Functor.isoWhiskerLeft F e.symm ≪≫ a) (.up ℤ)).inv.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app K) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerLeft F e.symm ≪≫ a) (.up ℤ)).inv.app K) =
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K))
  rw [← Functor.map_comp]
  congr 1
  ext n
  simp [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex]

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh
attribute [local irreducible] singleComplexOpenPullbackIso openPinnedTensorOpenIso

private theorem termwise_open_pinned_target_counit_triangle
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U' : X'.Opens)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (singleComplexOpenPullbackIso X' U').hom.app
        ((derivedPullback k).obj (DerivedCategory.Qh.obj P)) ≫
      (schemeOpenRestriction X' U').mapDerivedCategory.map
        ((pinnedPullbackCounit.{u, w} k).app P) ≫
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
        ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) =
    (pinnedPullbackComposition.{u, w} U'.ι k).hom.app (DerivedCategory.Qh.obj P) ≫
      (pinnedPullbackCounit.{u, w} (U'.ι ≫ k)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTargetCompositionIso k U').hom.app P) := by
  have : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
  let E : HomotopyCategory
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) (.up ℤ) :=
    ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ)).obj P
  let e := openPinnedTensorOpenIso X' U'
  let q := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace))
  let v := (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app E
  let vi := (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app E
  have ho := openCounit.{u, w} X' U' E
  have hi := mappedHomotopyInvHom e E q
  have ho' := targetOpenFactor
    ((singleComplexOpenPullbackIso X' U').inv.app (DerivedCategory.Qh.obj E))
    ((singleComplexOpenPullbackIso X' U').hom.app (DerivedCategory.Qh.obj E))
    ((pinnedPullbackCounit.{u, w} U'.ι).app E)
    ((schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app E)
    (q.map v) (q.map vi)
    ((singleComplexOpenPullbackIso X' U').inv_hom_id_app (DerivedCategory.Qh.obj E)) ho hi
  have hc := compositionCounit.{u, w} U'.ι k P
  have ht := termwise_targetHomotopyComparison e
    (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm P
  have hg := congrArg q.map ht
  simp only [q.map_comp] at hg
  have hn := (singleComplexOpenPullbackIso X' U').hom.naturality
    ((pinnedPullbackCounit.{u, w} k).app P)
  exact targetTriangleAlgebra _ _ _ _ _ _ _ _ _ _ _ hn.symm ho' hc hg

end CounitRestriction

section CounitCoherence

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

private theorem termwise_open_pinned_tensor_comparison_coherence
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (openPinnedHomotopyTargetCompositionIso k U').hom.app P ≫
      (termwise_openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P =
    eqToHom (congrArg (fun f ↦
      ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj P) hj).symm ≫
      (openPinnedHomotopySourceCompositionIso U j).hom.app P := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have ht : ∀ (f : U'.toScheme ⟶ X) (h : j ≫ U.ι = f),
      (Scheme.Modules.tensorPullbackCompositionIso j U.ι f h).hom =
        eqToHom (congrArg Scheme.Modules.tensorPullback h).symm ≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).hom := by
    intro f h
    cases h
    simp only [eqToHom_refl, Category.id_comp]
  have hb :
      (Functor.isoWhiskerLeft _ (openPinnedTensorOpenIso X' U').symm ≪≫
        (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm).inv ≫
        (openPinnedTensorRestrictionIso k U U' j hj).hom =
      eqToHom (congrArg Scheme.Modules.tensorPullback hj).symm ≫
        (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm _ ≪≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).symm).inv := by
    simp only [openPinnedTensorRestrictionIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [ht _ hj]
    simp only [Category.assoc, Functor.isoWhiskerRight_inv, Iso.symm_inv,
      Functor.isoWhiskerRight_hom]
  have := schemeOpenRestriction_additive X U
  have := schemeOpenRestriction_additive X' U'
  exact lift_comparison
    (fun f : U'.toScheme ⟶ X ↦ Scheme.Modules.tensorPullback f)
    (Scheme.Modules.tensorPullback k) (schemeOpenRestriction X' U')
    (schemeOpenRestriction X U) (Scheme.Modules.tensorPullback j) hj _ _ _ P hb

private theorem termwise_open_pinned_tensor_counit_transport
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    eqToHom (congrArg (fun f ↦ (derivedPullback f).obj (DerivedCategory.Qh.obj P)) hj) ≫
      (pinnedPullbackCounit.{u, w} (U'.ι ≫ k)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTargetCompositionIso k U').hom.app P) ≫
      DerivedCategory.Qh.map
        ((termwise_openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) =
    (pinnedPullbackCounit.{u, w} (j ≫ U.ι)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopySourceCompositionIso U j).hom.app P) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  exact transport_counit_comparison
    (fun f : U'.toScheme ⟶ X ↦ (derivedPullback.{u, w} f).obj (DerivedCategory.Qh.obj P))
    (fun f ↦ ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj P)
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace)))
    (fun f ↦ (pinnedPullbackCounit.{u, w} f).app P) hj _ _ _
    (termwise_open_pinned_tensor_comparison_coherence k U U' j hj P)

end CounitCoherence

private theorem termwise_open_pinned_counit_homotopy_restriction
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    singleComplexRestrictedCoefficient k (DerivedCategory.Qh.obj P)
        ((derivedPullback k).obj (DerivedCategory.Qh.obj P)) (𝟙 _) U U' j hj ≫
      (schemeOpenRestriction X' U').mapDerivedCategory.map
        ((pinnedPullbackCounit.{u, w} k).app P) ≫
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
        ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) ≫
      DerivedCategory.Qh.map
        ((termwise_openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (pinnedPullbackCounit.{u, w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P)  := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have ht := termwise_open_pinned_target_counit_triangle.{u, w} k U' P
  have hs := open_pinned_source_counit_triangle.{u, w} U j P
  have hc := termwise_open_pinned_tensor_counit_transport.{u, w} k U U' j hj P
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at ht hs hc
  have ht' := congrArg (fun f ↦ f ≫ DerivedCategory.Qh.map
    ((termwise_openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P)) ht
  simp only [Category.assoc] at ht'
  have h := counit_path_glue
    ((derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app
      (DerivedCategory.Qh.obj P)))
    ((pinnedPullbackComposition.{u, w} j U.ι).hom.app (DerivedCategory.Qh.obj P))
    (eqToHom (congrArg (fun f ↦ (derivedPullback f).obj (DerivedCategory.Qh.obj P)) hj))
    ((pinnedPullbackComposition.{u, w} U'.ι k).app (DerivedCategory.Qh.obj P))
    _ _ _ _ _ _ _ ht' hc hs
  simpa only [singleComplexRestrictedCoefficient, pinnedPullbackComposition, Iso.app_inv,
    CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc] using h

private theorem cancel_counit_factors
    {C : Type*} [Category C] {A B D E F G : C}
    (a : A ≅ B) (t : A ⟶ D) (e : D ⟶ E) (b : E ≅ F) (c : F ≅ G)
    (d : B ⟶ G) (h : t ≫ e ≫ b.hom ≫ c.hom = a.hom ≫ d) :
    a.inv ≫ t ≫ e = d ≫ c.inv ≫ b.inv := by
  have h' := congrArg (fun k => a.inv ≫ k ≫ c.inv ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.id_comp, Category.comp_id] using h'

set_option maxHeartbeats 600000 in
-- Elaborating the exact restriction localization factors needs this budget.
/-- The derived open coefficient on an actual restricted complex is compatible
with ordinary tensor pullback and the pinned counits. This is an equality before
stalks and cohomology; it needs neither a base-change square nor K-flatness.

Proof: specialize `open_pinned_counit_homotopy_restriction` to the homotopy
quotient of P. Its source exact-restriction factor is the complex localization
factor: expand `mapDerivedCategoryFactorsh_hom_app` and cancel the identity
quotient comparison maps. Precompose the equation with the inverse of this
factor mapped by Lj*. Postcompose with the inverse localized homotopy tensor
restriction isomorphism, then with the inverse target exact-restriction factor.
Cancel the three pairs of inverse isomorphisms. The resulting target composite
is exactly `singleComplexOpenTensorRestrictionMap`; the source composite uses
the canonical inverse representative factor a. This works for every complex,
before stalks or cohomology, with no inversion of a pullback counit. Empty and
top opens and zero complexes use the same natural-transformation identities.

Source: Stacks Project, cohomology.tex, Tags 08HY, 08FE and 0D5S;
perfect.tex, Tag 0DJ9, first paragraph.
(blueprint: lem-pc-single-complex-open-counit-compatibility). -/
theorem singleComplexOpen_termwise_counit_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    letI : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
    let K := DerivedCategory.Q.obj P
    let Q := ((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P
    let a := (schemeOpenRestriction X U).mapDerivedCategoryFactors.symm.app P
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      U U' j hj
    (derivedPullback j).map a.hom ≫ θ ≫
        (schemeOpenRestriction X' U').mapDerivedCategory.map
          ((counit g').app ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)) =
      (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) ≫
        singleComplexOpenTensorRestrictionMap g' U U' j hj P := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := fun k => tensorPullbackAdditive k
  have h := termwise_open_pinned_counit_homotopy_restriction g' U U' j hj
    ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)
  dsimp only [singleComplexOpenTensorRestrictionMap]
  have hf : (schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P) =
      (schemeOpenRestriction X U).mapDerivedCategoryFactors.hom.app P := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change (schemeOpenRestriction X U).mapDerivedCategory.map (𝟙 _) ≫
      (schemeOpenRestriction X U).mapDerivedCategoryFactors.hom.app P ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [(schemeOpenRestriction X U).mapDerivedCategory.map_id,
      DerivedCategory.Qh.map_id]
    simp only [Category.id_comp]
    exact Category.comp_id _
  rw [hf] at h
  have h' := cancel_counit_factors
    ((derivedPullback j).mapIso ((schemeOpenRestriction X U).mapDerivedCategoryFactors.app P))
    (singleComplexRestrictedCoefficient g' (DerivedCategory.Q.obj P)
      ((derivedPullback g').obj (DerivedCategory.Q.obj P)) (𝟙 _) U U' j hj)
    ((schemeOpenRestriction X' U').mapDerivedCategory.map
      ((counit g').app ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    ((schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.app
      (((Scheme.Modules.tensorPullback g').mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    (DerivedCategory.Qh.mapIso
      ((termwise_openPinnedHomotopyTensorRestrictionIso g' U U' j hj).app
        ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    ((counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P)))
    (by
      change _ = _ at h
      exact h)
  simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.symm_hom, Iso.app_hom] using h'

end AlgebraicGeometry
