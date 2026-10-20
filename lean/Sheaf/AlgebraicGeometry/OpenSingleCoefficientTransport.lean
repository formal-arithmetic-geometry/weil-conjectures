/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleTensorRestrictionFactors
import Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts

/-! # Coefficient transport along an isomorphic apex over an open subscheme

Source: Stacks Project, Tags 06YJ and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

set_option linter.flexible false in
-- The degree-zero single-object identifications are normalized before changing the goal.
private theorem single_iso_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (M : C) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M =
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app M) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single_map_f_self]
    change e.hom.app M ≫ 𝟙 _ = 𝟙 _ ≫ e.hom.app M ≫ 𝟙 _
    simp only [Category.id_comp]
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

private theorem cancel {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
      {X Y : D} {U V : C} (e : X ⟶ Y) (q : Y ⟶ F.obj U) (b : U ≅ V) :
      (e ≫ q ≫ F.map b.hom) ≫ F.map b.inv = e ≫ q := by
  simp only [Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id, Category.comp_id]

private theorem mapIdentityCounit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ E) (Q : D ⥤ E) {A : C} {B : D} (e : L.obj A ⟶ Q.obj B) :
    L.map (𝟙 A) ≫ e ≫ Q.map (𝟙 B) ≫ 𝟙 (Q.obj B) = e := by
  simp only [L.map_id, Q.map_id, Category.comp_id, Category.id_comp]

variable [dc : ∀ Y : Scheme.{u}, HasDerivedCategory.{u + 1}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [add : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), (Scheme.Modules.tensorPullback f).Additive]

private instance modulesDerived (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  dc X

attribute [local irreducible] derivedPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.tensorPullback

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules
attribute [local implicit_reducible] Scheme.Modules.Hom DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh

set_option maxHeartbeats 800000 in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem open_counit_factor
    (X : Scheme.{u}) (U : X.Opens)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (singleComplexOpenPullbackIso X U).inv.app (DerivedCategory.Qh.obj P) ≫
        (pinnedPullbackCounit.{u, u + 1} U.ι).app P =
      (schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (openPinnedTensorOpenIso X U).inv (.up ℤ)).app P) := by
  classical
  let T : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  let e : schemeOpenRestriction X U ≅ T := (openPinnedTensorOpenIso X U).symm
  have : PreservesFiniteLimits (schemeOpenRestriction X U) :=
    schemeOpenRestriction_preservesFiniteLimits X U
  have : PreservesFiniteColimits (schemeOpenRestriction X U) :=
    schemeOpenRestriction_preservesFiniteColimits X U
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso e
  have hL := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition))) U.ι
  have := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  have he := Functor.mapDerivedCategoryNatIso_fach e P
  dsimp only [singleComplexOpenPullbackIso, Iso.trans_inv, NatTrans.comp_app]
  have hθ : Scheme.Modules.overFunctorEquiv U ≪≫
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
          (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm).symm = e := by
    simp only [e, openPinnedTensorOpenIso, Iso.trans_symm,
      Iso.symm_symm_eq, Iso.trans_assoc]
  rw [hθ]
  simp only [Iso.symm_inv, Category.assoc, Functor.leftDerivedUnique,
    Functor.leftDerivedNatIso_inv, Functor.leftDerivedNatTrans_app,
    Iso.refl_inv, NatTrans.id_app, Category.comp_id]
  exact he

set_option maxHeartbeats 800000 in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem q_normalize {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    Scheme.picardTermwiseSingleMap f M =
      (pinnedPullbackCounit.{u,u+1} f).app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.app M)) := by
  let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  exact cancel (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0) _ _ (t.app M)

attribute [local irreducible] singleComplexOpenPullbackIso Scheme.picardTermwiseSingleMap
  Scheme.picardTermwiseCounit

omit add
set_option maxHeartbeats 800000 in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem open_single_factor (Y : Scheme.{u}) (U : Y.Opens) (M : Y.Modules) :
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
    let ρ := (openPinnedTensorOpenIso Y U).app M ≪≫ (Scheme.Modules.overFunctorEquiv U).app M
    (singleComplexOpenPullbackIso Y U).hom.app K ≫
      ((schemeOpenRestriction Y U).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map ((Scheme.Modules.overFunctorEquiv U).hom.app M) =
    Scheme.picardTermwiseSingleMap U.ι M ≫ (DerivedCategory.singleFunctor _ 0).map ρ.hom := by
  classical
  let := fun {A B : Scheme.{u}} (f : A ⟶ B) ↦
    (Classical.choose exists_derivedPullbackComposition) f
  dsimp only
  rw [q_normalize]
  apply (cancel_epi ((singleComplexOpenPullbackIso Y U).inv.app _)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have ho := open_counit_factor Y U ((HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
  change (singleComplexOpenPullbackIso Y U).inv.app
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫ _ = _ at ho
  rw [← Category.assoc ((singleComplexOpenPullbackIso Y U).inv.app _), ho]
  have hc := single_iso_naturality (openPinnedTensorOpenIso Y U).symm M
  have hh := congrArg (fun f ↦ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient _ (.up ℤ)).map f)) hc
  simp only [Functor.map_comp] at hh
  change DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory (openPinnedTensorOpenIso Y U).inv (.up ℤ)).app
        ((HomotopyCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback U.ι) (.up ℤ) 0).hom.app M)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (schemeOpenRestriction Y U) (.up ℤ) 0).hom.app M)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((openPinnedTensorOpenIso Y U).inv.app M) at hh
  have hs := (open_pinned_single_tensor_restriction_factors
    (𝟙 Y) U U (𝟙 U.toScheme) (by simp) M).1
  simp only [Category.assoc]
  erw [reassoc_of% hh]
  rw [← Functor.map_comp]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, hs]

include add
set_option maxHeartbeats 800000 in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem counit_normalize {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    (Scheme.picardTermwiseCounit f).app K =
      (pinnedPullbackCounit.{u,u+1} f).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) := by
  simp only [Scheme.picardTermwiseCounit, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  exact mapIdentityCounit (derivedPullback f) DerivedCategory.Qh _

set_option maxHeartbeats 800000 in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem q_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (m : M ⟶ N) :
    (derivedPullback f).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map m) ≫
      Scheme.picardTermwiseSingleMap f N =
    Scheme.picardTermwiseSingleMap f M ≫ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
        ((Scheme.Modules.tensorPullback f).map m) := by
  simp only [q_normalize f N, q_normalize f M, Category.assoc]
  rw [← Category.assoc]
  have hn := (pinnedPullbackCounit.{u,u+1} f).naturality
    ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map m)
  change (derivedPullback f).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map m) ≫ _ = _ at hn
  have hn' := congrArg (fun a ↦ a ≫ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.app N))) hn
  rw [hn']
  simp only [Category.assoc]
  congr 1
  have hs := (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.naturality m
  have hh := congrArg (fun h ↦ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient _ (.up ℤ)).map h)) hs
  dsimp only [Functor.comp_map] at hh
  simp only [DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    Functor.comp_map]
  erw [Functor.mapHomotopyCategory_map]
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
    (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.single
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ) 0).map m))) ≫ _ = _
  simp only [Functor.map_comp, Functor.comp_obj] at hh
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at hh
  exact hh

set_option maxHeartbeats 800000 in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem q_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : X ⟶ Z) (ht : f ≫ g = t) (M : Z.Modules) :
    (relativeMVComp f g).hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M) ≫
      eqToHom (congrArg (fun a ↦ (derivedPullback a).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M)) ht) ≫
      Scheme.picardTermwiseSingleMap t M ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((Scheme.Modules.tensorPullbackCompositionIso f g t ht).hom.app M) =
    (derivedPullback f).map (Scheme.picardTermwiseSingleMap g M) ≫
      Scheme.picardTermwiseSingleMap f ((Scheme.Modules.tensorPullback g).obj M) := by
  subst t
  simp only [eqToHom_refl, Category.id_comp]
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let z := DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.tensorPullback f) (.up ℤ) 0).app
      ((Scheme.Modules.tensorPullback g).obj M))
  let c := relativeMVComp f g
  have h := Scheme.picardTermwiseSingleMap_composition f g (f ≫ g) rfl M
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, eqToIso_refl, Iso.trans_refl] at h
  change c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M) ≫
      Scheme.picardTermwiseSingleMap (f ≫ g) M ≫
      S.map ((Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).hom.app M) ≫ z.inv =
    (derivedPullback f).map (Scheme.picardTermwiseSingleMap g M) ≫
      (Scheme.picardTermwiseCounit f).app ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback g).obj M)) at h
  have hh := congrArg (fun a ↦ a ≫ z.hom) h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [counit_normalize] at hh
  have hq := q_normalize f ((Scheme.Modules.tensorPullback g).obj M)
  change Scheme.picardTermwiseSingleMap f ((Scheme.Modules.tensorPullback g).obj M) =
    (pinnedPullbackCounit.{u,u+1} f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback g).obj M))) ≫ z.hom at hq
  rw [← hq] at hh
  simpa only [S, c, z, Functor.mapIso_hom, Category.assoc] using hh

set_option maxHeartbeats 800000 in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem q_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso (Scheme.picardTermwiseSingleMap f M) := by
  rw [q_normalize]
  have hc := SingleComplexBaseChange.isIso_counit_of_isIso f
    ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
  change IsIso ((pinnedPullbackCounit.{u,u+1} f).app
    ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)) at hc
  infer_instance

omit add
set_option maxHeartbeats 800000 in
-- The selected counits have large dependent types; keep their data abstract.
/-- The single-complex coefficient square for restriction and an isomorphic apex.
Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-pc-open-single-coefficient-transport)

Proof: Let j be U.ι and ρ the canonical tensor-pullback-to-restriction comparison,
obtained from the unique comparison of the tensor adjunction to the restriction
adjunction. The displayed a equals q_j(M) followed by single.map ρ.hom: expand
singleComplexOpenPullbackIso using uniqueness of the left-derived functor and
its factorization at a single complex. Construct b : tensorPullback k.hom
(tensorPullback r M) ≅ tensorPullback r' (M.restrict j) from the inverse tensor
composition comparison for (k.hom,r), transport by hr, the composition comparison
for (r',j), and tensorPullback r' of ρ. Tensor pullback along an isomorphism is
exact, so its left-derived counit on a single is invertible. Set d to this
invertible single comparison for k.hom, followed by single.mapIso b. Apply
picardTermwiseSingleMap_composition first to (k.hom,r), then to (r',j). The tensor
composition factors are precisely b's factors. Cancel their inverses and use
naturality for ρ. This gives the asserted coefficient equation. No base-change
map or direct image is used. Empty opens, empty schemes and zero modules satisfy
the same construction and identities. -/
theorem exists_openSingle_coefficient_transport
    {Y P P' : Scheme.{u}} (U : Y.Opens) (M : Y.Modules)
    (r : P ⟶ Y) (r' : P' ⟶ U.toScheme) (k : P' ≅ P)
    (hr : k.hom ≫ r = r' ≫ U.ι) :
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
    let N := M.restrict U.ι
    let a : (derivedPullback U.ι).obj K ≅
        (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj N :=
      (singleComplexOpenPullbackIso Y U).app K ≪≫
        ((schemeOpenRestriction Y U).mapDerivedCategorySingleFunctor 0).app M ≪≫
        (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).mapIso
          ((Scheme.Modules.overFunctorEquiv U).app M)
    let T := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
      ((Scheme.Modules.tensorPullback r).obj M)
    let T' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P'.toRingedSpace)) 0).obj
      ((Scheme.Modules.tensorPullback r').obj N)
    ∃ d : (derivedPullback k.hom).obj T ≅ T',
      (derivedPullback k.hom).map (Scheme.picardTermwiseSingleMap r M) ≫ d.hom =
        (relativeMVComp k.hom r).hom.app K ≫
          eqToHom (congrArg (fun f ↦ (derivedPullback f).obj K) hr) ≫
          (relativeMVComp r' U.ι).inv.app K ≫ (derivedPullback r').map a.hom ≫
          Scheme.picardTermwiseSingleMap r' N := by
  classical
  let := fun {A B : Scheme.{u}} (f : A ⟶ B) ↦
    (Classical.choose exists_derivedPullbackComposition) f
  dsimp only
  let δ₁ := (Scheme.Modules.tensorPullbackCompositionIso k.hom r (r' ≫ U.ι) hr).app M
  let δ₂ := (Scheme.Modules.tensorPullbackCompositionIso r' U.ι (r' ≫ U.ι) rfl).app M
  let ρ := (openPinnedTensorOpenIso Y U).app M ≪≫ (Scheme.Modules.overFunctorEquiv U).app M
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings P'.toRingedSpace)) 0
  let b := δ₁.symm ≪≫ δ₂ ≪≫ (Scheme.Modules.tensorPullback r').mapIso ρ
  have : IsIso (Scheme.picardTermwiseSingleMap k.hom
      ((Scheme.Modules.tensorPullback r).obj M)) := q_isIso _ _
  refine ⟨asIso (Scheme.picardTermwiseSingleMap k.hom
    ((Scheme.Modules.tensorPullback r).obj M)) ≪≫ S.mapIso b, ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  have h₁ := q_composition k.hom r (r' ≫ U.ι) hr M
  have h₂ := q_composition r' U.ι (r' ≫ U.ι) rfl M
  have hρ := q_naturality r' ρ.hom
  have ha := open_single_factor Y U M
  simp only [eqToHom_refl, Category.id_comp] at h₂
  have hb : S.map δ₁.hom ≫ S.map b.hom =
      S.map δ₂.hom ≫ S.map ((Scheme.Modules.tensorPullback r').map ρ.hom) := by
    rw [← S.map_comp, ← S.map_comp]
    congr 1
    simp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.hom_inv_id_assoc]
  have h₂' := congrArg (fun f ↦
    (relativeMVComp r' U.ι).inv.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫ f) h₂
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at h₂'
  rw [← Category.assoc, ← h₁]
  simp only [Category.assoc]
  erw [hb]
  erw [reassoc_of% h₂']
  erw [← hρ]
  rw [← Functor.map_comp_assoc]
  erw [← ha]
  rfl

end AlgebraicGeometry

