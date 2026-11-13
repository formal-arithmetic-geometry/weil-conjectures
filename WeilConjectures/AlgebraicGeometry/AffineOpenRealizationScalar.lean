/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import WeilConjectures.AlgebraicGeometry.AffineSheafificationScalar

/-! # Scalar compatibility of affine realization

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem scalar_iso_conjugate {S : Type*} [Ring S] {C : Type*}
    [Category C] [Preadditive C] [Linear S C] {V W : C} (r : S) (d : V ≅ W) :
    r • 𝟙 W = d.inv ≫ (r • 𝟙 V) ≫ d.hom := by
  simp

private theorem scalar_commute {S : Type*} [Ring S] {C : Type*}
    [Category C] [Preadditive C] [Linear S C] {V W : C} (r : S) (f : V ⟶ W) :
    (r • 𝟙 V) ≫ f = f ≫ (r • 𝟙 W) := by
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1600000 in
-- The scalar action is transported through the derived localization.
private theorem restriction_scalar (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (a : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    let B := (Over.forget U).op ⋙ X.sheaf.obj
    letI : Linear (RingCat.sectionsSubring (B ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
      SheafOfModules.homLinear B ((moduleRings X.toRingedSpace).over U).property
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    R.map (schemeDerivedScalar X a (𝟙 E)) =
      PresheafOfModules.overSections (R := X.sheaf.obj) U (a.val (op U)) • 𝟙 (R.obj E) := by
  intro B R
  let : Linear (RingCat.sectionsSubring (B ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.homLinear B ((moduleRings X.toRingedSpace).over U).property
  let b := PresheafOfModules.overSections (R := X.sheaf.obj) U (a.val (op U))
  let : Linear
      (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
  let T := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  have hbase (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
      T.map (a • 𝟙 M) = b • 𝟙 (T.obj M) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    change a.val (op V.unop.left) • x =
      X.sheaf.obj.map V.unop.hom.op (a.val (op U)) • x
    exact congrArg (fun r ↦ r • x) (a.property V.unop.hom.op).symm
  have hcomplex (L : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
      (T.mapHomologicalComplex (.up ℤ)).map (a • 𝟙 L) =
        b • 𝟙 ((T.mapHomologicalComplex (.up ℤ)).obj L) := by
    apply HomologicalComplex.hom_ext
    intro n
    exact hbase (L.X n)
  have hQ (L : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
      R.map (a • 𝟙 (DerivedCategory.Q.obj L)) =
        b • 𝟙 (R.obj (DerivedCategory.Q.obj L)) := by
    let c := T.mapDerivedCategoryFactors.app L
    apply (cancel_mono c.hom).mp
    have hc := T.mapDerivedCategoryFactors.hom.naturality (a • 𝟙 L)
    change R.map (DerivedCategory.Q.map (a • 𝟙 L)) ≫ c.hom =
      c.hom ≫ DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map (a • 𝟙 L))
      at hc
    rw [DerivedCategory.Q.map_smul a (𝟙 L), CategoryTheory.Functor.map_id,
      hcomplex L, DerivedCategory.Q.map_smul b (𝟙 _),
      CategoryTheory.Functor.map_id] at hc
    exact hc.trans (scalar_commute b c.hom).symm
  let L := DerivedCategory.Q.objPreimage E
  let d := DerivedCategory.Q.objObjPreimageIso E
  have hd : a • 𝟙 E = d.inv ≫ (a • 𝟙 (DerivedCategory.Q.obj L)) ≫ d.hom :=
    scalar_iso_conjugate a d
  change R.map (a • 𝟙 E) = _
  rw [hd, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hQ L]
  exact (scalar_iso_conjugate b (R.mapIso d)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 900000 in
-- Sectionwise scalar actions require unfolding transported module structures.
/-- Scalar identities commute with every affine realization comparison isomorphism.
This requires neither perfectness nor a cohomology support condition (Stacks, Tags 06Z0 and 08EJ).
-/
theorem affine_open_realization_scalar
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) →
      ∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (E : schemeDerivedCategory X)
        (e : F.obj (DerivedCategory.Q.obj K) ≅ R.obj E)
        (a : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})),
        F.map ((show A from a.val (op U)) • 𝟙 (DerivedCategory.Q.obj K)) ≫ e.hom =
          e.hom ≫ R.map (schemeDerivedScalar X a (𝟙 E)) := by
  intro A R F hF K E e a
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  let B := (Over.forget U).op ⋙ X.sheaf.obj
  let : Linear
      (RingCat.sectionsSubring (B ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.homLinear B ((moduleRings X.toRingedSpace).over U).property
  let b := PresheafOfModules.overSections (R := X.sheaf.obj) U (a.val (op U))
  have he : (b • 𝟙 (F.obj (DerivedCategory.Q.obj K))) ≫ e.hom =
      e.hom ≫ (b • 𝟙 (R.obj E)) := scalar_commute b e.hom
  have hR : R.map (schemeDerivedScalar X a (𝟙 E)) = b • 𝟙 (R.obj E) :=
    restriction_scalar X U E a
  let S := affinePerfectSheafification X U hU
  have hS : (S.mapHomologicalComplex (.up ℤ)).map ((show A from a.val (op U)) • 𝟙 K) =
      b • 𝟙 ((S.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply HomologicalComplex.hom_ext
    intro n
    exact affine_perfect_sheafification_scalar X U hU (K.X n) (a.val (op U))
  obtain ⟨c⟩ := hF
  have hFscalar : F.map ((show A from a.val (op U)) • 𝟙 (DerivedCategory.Q.obj K)) =
      b • 𝟙 (F.obj (DerivedCategory.Q.obj K)) := by
    apply (cancel_mono (c.hom.app K)).mp
    have hc := c.hom.naturality ((show A from a.val (op U)) • 𝟙 K)
    change F.map (DerivedCategory.Q.map ((show A from a.val (op U)) • 𝟙 K)) ≫
        c.hom.app K =
      c.hom.app K ≫ DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map
        ((show A from a.val (op U)) • 𝟙 K)) at hc
    rw [DerivedCategory.Q.map_smul (show A from a.val (op U)) (𝟙 K),
      CategoryTheory.Functor.map_id, hS,
      DerivedCategory.Q.map_smul b (𝟙 _), CategoryTheory.Functor.map_id] at hc
    exact hc.trans (scalar_commute b (c.hom.app K)).symm
  rw [hFscalar, hR]
  exact he

end AlgebraicGeometry.Scheme
