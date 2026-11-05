/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.IsomorphicSingleTensorCounitTransport
import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
/-! # Counit equation for canonical transport
Source: Stacks Project, Tags 08HY, 0096 and 0D5S.
(blueprint: lem-pc-isomorphic-single-tensor-counit-equation). -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback

private theorem single_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomologicalComplexCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N =
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
        (F.obj N) ≫
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (c.hom.app N) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [HomologicalComplex.singleMapHomologicalComplex,
    HomologicalComplex.single, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
    Functor.mapHomologicalComplex]

private theorem homotopy_single_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomotopyCategoryCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.singleFunctor A 0).obj N) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N) =
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N)) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
          (F.obj N)) ≫
      (HomotopyCategory.singleFunctor C 0).map (c.hom.app N) := by
  have hs := single_comp F G H c N
  have hq := congrArg
    (fun k ↦ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map k) hs
  simpa only [Functor.map_comp, Functor.mapHomotopyCategory_map,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, CochainComplex.singleFunctors, Functor.comp_map,
    Functor.comp_obj, Functor.mapHomotopyCategoryCompIso,
    Quotient.natIsoLift_hom, Functor.isoWhiskerRight_hom, Quotient.natTransLift,
    Functor.whiskerRight_app, HomotopyCategory.quotient_obj_as, Category.assoc] using hq

private def tensorAdjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f :=
  Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)

private def tensorCompositionComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.tensorPullback (f ≫ g) :=
  (conjugateIsoEquiv
    (tensorAdjunction (f ≫ g))
    ((tensorAdjunction g).comp
      (tensorAdjunction f))).symm
        (Scheme.Modules.pushforwardComp f g).symm

private def tensorCounit
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  pinnedPullbackCounit.{u, w} f

private theorem transport_eq
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {K B : C} {A : D} (q : K ⟶ B) (r : L.obj B ⟶ A) (t : R.obj A ≅ B)
    (ht : t.inv = a.unit.app B ≫ R.map r) :
    a.unit.app K ≫ R.map (L.map q ≫ r) ≫ t.hom = q := by
  simp only [R.map_comp, ← Category.assoc]
  rw [a.unit_naturality q]
  rw [Category.assoc q (a.unit.app B) (R.map r), ← ht]
  simp only [Category.assoc, t.inv_hom_id, Category.comp_id]


end AlgebraicGeometry
