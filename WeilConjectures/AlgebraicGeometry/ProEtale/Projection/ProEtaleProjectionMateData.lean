/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorExact
import WeilConjectures.AlgebraicGeometry.SignedProjectionResolution.SignedProjectionResolutionNormalization
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Natural transformation and unit normalization of the pro-etale projection mate

Source: Stacks, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56.
(blueprint: lem-weil-pbc-proetale-projection-mate-data-s4).

The shifts are constructed together with the mate, by transport from the normalized
model. Arbitrary independently chosen shift structures do not suffice.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))

private def fixedRestrictionIso
    {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ C) (T' : D × D ⥤ D) (r : C ⥤ D)
    (t : T ⋙ r ≅ (r.prod r) ⋙ T') (E : C) :
    (Functor.curryObj T).obj E ⋙ r ≅ r ⋙ (Functor.curryObj T').obj (r.obj E) :=
  NatIso.ofComponents (fun P ↦ t.app (E, P)) (by
    intro P Q h
    change r.map (T.map (Prod.mkHom (𝟙 E) h)) ≫ t.hom.app (E, Q) =
      t.hom.app (E, P) ≫ T'.map (Prod.mkHom (𝟙 (r.obj E)) (r.map h))
    have ht := t.hom.naturality (Prod.mkHom (𝟙 E) h)
    change r.map (T.map (Prod.mkHom (𝟙 E) h)) ≫ t.hom.app (E, Q) =
      t.hom.app (E, P) ≫ T'.map (Prod.mkHom (r.map (𝟙 E)) (r.map h)) at ht
    rw [r.map_id] at ht
    exact ht)

private def operationMate
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R' : Sheaf J CommRingCat.{u + 1}}
    {S' : Sheaf K CommRingCat.{u + 1}}
    (o : ProjectionRestriction.Operation F R' S')
    (a' : ProjectionRestriction.TensorModel R') (b' : ProjectionRestriction.TensorModel S')
    (t : a'.functor ⋙ o.left ≅ (o.left.prod o.left) ⋙ b'.functor)
    (E' : ProjectionRestriction.Der S') :
    (Functor.curry.obj a'.functor).obj (o.right.obj E') ⟶
      o.left ⋙ (Functor.curry.obj b'.functor).obj E' ⋙ o.right :=
  let A := (Functor.curry.obj a'.functor).obj (o.right.obj E')
  let beta := (fixedRestrictionIso a'.functor b'.functor o.left t (o.right.obj E')).hom ≫
      Functor.whiskerLeft o.left
        ((Functor.curry.obj b'.functor).map (o.derivedAdjunction.counit.app E'))
  A.rightUnitor.inv ≫ Functor.whiskerLeft A o.derivedAdjunction.unit ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight beta o.right ≫
      (Functor.associator o.left ((Functor.curry.obj b'.functor).obj E') o.right).hom

private theorem operationMate_eq
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R' : Sheaf J CommRingCat.{u + 1}}
    {S' : Sheaf K CommRingCat.{u + 1}}
    (o : ProjectionRestriction.Operation F R' S')
    (a' : ProjectionRestriction.TensorModel R') (b' : ProjectionRestriction.TensorModel S')
    (t : a'.functor ⋙ o.left ≅ (o.left.prod o.left) ⋙ b'.functor)
    (E' : ProjectionRestriction.Der S') (P : ProjectionRestriction.Der R') :
    (operationMate o a' b' t E').app P =
      derivedProjectionFormulaMate o.left o.right o.derivedAdjunction
        a'.functor b'.functor t E' P := by
  simp [operationMate, fixedRestrictionIso, derivedProjectionFormulaMate,
    Adjunction.rightAdjointProjectionMap_app_app, Adjunction.homEquiv_unit,
    Functor.map_comp]

private theorem operationMate_commShift
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R' : Sheaf J CommRingCat.{u + 1}}
    {S' : Sheaf K CommRingCat.{u + 1}}
    (o : ProjectionRestriction.Operation F R' S')
    [o.right.CommShift ℤ] [o.derivedAdjunction.CommShift ℤ]
    (a' : ProjectionRestriction.TensorModel R') (b' : ProjectionRestriction.TensorModel S')
    [sa : ProjectionRestriction.TensorShifts a'] [sb : ProjectionRestriction.TensorShifts b']
    (mu : o.OrdinaryTensor)
    (t : ProjectionRestriction.TensorComparison o.pullback o.leftModel a' b' mu.iso)
    (hs : ProjectionRestriction.TensorComparisonShifts t)
    (E' : ProjectionRestriction.Der S') :
    NatTrans.CommShift (operationMate o a' b' t.comparison E') ℤ := by
  let A := (Functor.curry.obj a'.functor).obj (o.right.obj E')
  let m : A ⋙ o.left ⟶ o.left ⋙
      (Functor.curry.obj b'.functor).obj (o.left.obj (o.right.obj E')) :=
    (fixedRestrictionIso a'.functor b'.functor o.left t.comparison (o.right.obj E')).hom
  have : NatTrans.CommShift m ℤ := by
    constructor
    intro n
    ext P
    simpa only [m, A, fixedRestrictionIso, NatIso.ofComponents_hom_app, Iso.app_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
      Functor.curry_obj_obj_map, Functor.curry_obj_obj_obj, Category.assoc] using
      (hs.second (o.right.obj E') P n).symm
  let beta : A ⋙ o.left ⟶ o.left ⋙ (Functor.curry.obj b'.functor).obj E' :=
    m ≫ Functor.whiskerLeft o.left
      ((Functor.curry.obj b'.functor).map (o.derivedAdjunction.counit.app E'))
  have : NatTrans.CommShift beta ℤ := by dsimp only [beta]; infer_instance
  change NatTrans.CommShift (A.rightUnitor.inv ≫
    Functor.whiskerLeft A o.derivedAdjunction.unit ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight beta o.right ≫
      (Functor.associator o.left ((Functor.curry.obj b'.functor).obj E') o.right).hom) ℤ
  infer_instance

end AlgebraicGeometry.Scheme
