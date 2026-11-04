/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionPullTensorDelta
public import WeilConjectures.AlgebraicGeometry.CompositeModuleOplaxMate
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison

/-! # The pullback tensorator on unit sections of tensor generators -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.monoidal_upperStar

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Local pure tensors are natural for tensor products of module maps. -/
theorem internalPureTensor_tensorHom (X : Scheme.{u}) {M M' N N' : internalModules Λ X}
    (g : M ⟶ M') (g' : N ⟶ N') (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((g ⊗ₘ g').hom.hom.app U) (internalPureTensor Λ X M N U x y) =
      internalPureTensor Λ X M' N' U (g.hom.hom.app U x) (g'.hom.hom.app U y) :=
  InternalAbelianSheafModule.comparison_internalTmul_natural _ _ g g' U x y

omit [IsCommMonObj Λ] in
/-- Sections of a composite of internal module maps. -/
theorem internalModules_comp_apply {X : Scheme.{u}} {M N K : internalModules Λ X}
    (g : M ⟶ N) (g' : N ⟶ K) (U : X.ProEtᵒᵖ) (z : M.X.obj.obj U) :
    (g ≫ g').hom.hom.app U z = g'.hom.hom.app U (g.hom.hom.app U z) :=
  rfl

omit [IsCommMonObj Λ] in
/-- Internal direct image acts on sections by evaluation at the base-changed object. -/
theorem lowerStar_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : internalModules Λ X}
    (g : M ⟶ N) (U : Y.ProEtᵒᵖ) (z : ((CondensedRing.lowerStar Λ f).obj M).X.obj.obj U) :
    ((CondensedRing.lowerStar Λ f).map g).hom.hom.app U z =
      g.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj U) z :=
  rfl

/-- The specified direct-image pairing sends local pure tensors to local pure tensors. -/
theorem internalPushLax_μ_internalPureTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((CondensedRing.lowerStar Λ f).obj M).X.obj.obj U)
    (y : ((CondensedRing.lowerStar Λ f).obj N).X.obj.obj U) :
    (((internalPushLax Λ f).μ M N).hom.hom.app U) (internalPureTensor Λ Y _ _ U x y) =
      internalPureTensor Λ X M N ((Scheme.proEtaleBaseChange f).op.obj U) x y :=
  (internalPushNormalized_existsUnique Λ f).exists.choose_spec M N U x y

/-- The inverse ordinary tensor comparison sends sheafified pure tensors to internal ones. -/
theorem ordinaryTensorComparison_inv_sectionPureTensor (X : Scheme.{u})
    (M N : internalModules Λ X) (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((ordinaryTensorComparison Λ X M N).inv.val.app U)
        (sectionPureTensor Λ X ((equivalence Λ X).functor.obj M)
          ((equivalence Λ X).functor.obj N) U x y) =
      internalPureTensor Λ X M N U x y := by
  rw [← (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec U x y]
  exact congrArg (fun g ↦ g.val.app U (internalPureTensor Λ X M N U x y))
    (ordinaryTensorComparison Λ X M N).hom_inv_id

/-- The oplax tensorator of the module pullback, evaluated on unit images of pure tensors. -/
theorem upperStar_δ_unit_internalPureTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) (U : Y.ProEt) (x : M.X.obj.obj (op U))
    (y : N.X.obj.obj (op U)) :
    (((CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N).hom.hom.app
        ((Scheme.proEtaleBaseChange f).op.obj (op U)))
      (((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app (M ⊗ N)).hom.hom.app (op U)
        (internalPureTensor Λ Y M N (op U) x y)) =
    internalPureTensor Λ X _ _ ((Scheme.proEtaleBaseChange f).op.obj (op U))
      (((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom.hom.app (op U) x)
      (((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app N).hom.hom.app (op U) y) := by
  have h := congrArg (fun g ↦ g.hom.hom.app (op U) (internalPureTensor Λ Y M N (op U) x y))
    ((composite_module_oplax_mate Λ f).1 M N)
  rw [Adjunction.homEquiv_unit] at h
  dsimp only [Functor.comp_obj, Functor.id_obj] at h ⊢
  rw [internalModules_comp_apply, internalModules_comp_apply] at h
  rw [lowerStar_map_apply] at h
  rw [internalPureTensor_tensorHom] at h
  rw [internalPushLax_μ_internalPureTensor] at h
  exact h

end AlgebraicGeometry.ProEtale.ModuleRingedComparison

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The section-module equivalence does not change sections of maps. -/
theorem spIntegralModuleEquivalence_map_apply (T : Scheme.{u}) {M N : Modules l E T}
    (g : M ⟶ N) (U : T.ProEtᵒᵖ)
    (z : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    ((spIntegralModuleEquivalence l E T).functor.map g).val.app U z = g.hom.hom.app U z :=
  rfl

/-- A tensor generator is the summand inclusion of an internal local pure tensor. -/
theorem tensorGenerator_eq (T : Scheme.{u}) (P Q : CochainComplex (Modules l E T) ℤ)
    (a b k : ℤ) (h : a + b = k) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj (P.X a)).val.obj U)
    (y : ((spIntegralModuleEquivalence l E T).functor.obj (Q.X b)).val.obj U) :
    tensorGenerator l E T P Q a b k h U x y =
      (HomologicalComplex.ιTensorObj P Q a b k h).hom.hom.app U
        (ModuleRingedComparison.internalPureTensor (spIntegralCondensed l E) T
          (P.X a) (Q.X b) U x y) := by
  rw [← ModuleRingedComparison.ordinaryTensorComparison_inv_sectionPureTensor]
  rfl

set_option maxHeartbeats 400000 in
-- Matching the pulled-back tensor generator unfolds large coefficient instances.
/-- The degreewise pullback tensorator sends the unit image of a tensor generator to the
tensor generator of the unit images. -/
theorem pullTensorChain_unit_tensorGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (Modules l E Y) ℤ) (a b k : ℤ) (h : a + b = k) (U : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj (P.X a)).val.obj (op U))
    (y : ((spIntegralModuleEquivalence l E Y).functor.obj (Q.X b)).val.obj (op U)) :
    ((spIntegralModuleEquivalence l E X).functor.map ((pullTensorChain l E f P Q).f k)).val.app
        (op ((Scheme.proEtaleBaseChange f).obj U))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          ((P ⊗ Q).X k)).hom.hom.app (op U) (tensorGenerator l E Y P Q a b k h (op U) x y)) =
    tensorGenerator l E X (((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P)
      (((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj Q) a b k h
      (op ((Scheme.proEtaleBaseChange f).obj U))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          (P.X a)).hom.hom.app (op U) x)
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          (Q.X b)).hom.hom.app (op U) y) := by
  let := (CondensedRing.monoidal_upperStar (spIntegralCondensed l E) f).toOplaxMonoidal
  -- The unit is natural and the tensorator restricts to `δ` on the summand `(a, b)`.
  have key : HomologicalComplex.ιTensorObj P Q a b k h ≫
      (CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        ((P ⊗ Q).X k) ≫
      (CondensedRing.lowerStar (spIntegralCondensed l E) f).map
        ((pullTensorChain l E f P Q).f k) =
      (CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        (P.X a ⊗ Q.X b) ≫
      (CondensedRing.lowerStar (spIntegralCondensed l E) f).map
        (Functor.OplaxMonoidal.δ (CondensedRing.upperStar (spIntegralCondensed l E) f)
          (P.X a) (Q.X b)) ≫
      (CondensedRing.lowerStar (spIntegralCondensed l E) f).map
        (HomologicalComplex.ιTensorObj
          (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
            (.up ℤ)).obj P)
          (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
            (.up ℤ)).obj Q) a b k h) := by
    have h1 : HomologicalComplex.ιTensorObj P Q a b k h ≫
        (CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          ((P ⊗ Q).X k) =
        (CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          (P.X a ⊗ Q.X b) ≫
        (CondensedRing.lowerStar (spIntegralCondensed l E) f).map
          ((CondensedRing.upperStar (spIntegralCondensed l E) f).map
            (HomologicalComplex.ιTensorObj P Q a b k h)) :=
      (CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.naturality
        (HomologicalComplex.ιTensorObj P Q a b k h)
    have h2 : (CondensedRing.upperStar (spIntegralCondensed l E) f).map
          (HomologicalComplex.ιTensorObj P Q a b k h) ≫ (pullTensorChain l E f P Q).f k =
        Functor.OplaxMonoidal.δ (CondensedRing.upperStar (spIntegralCondensed l E) f)
          (P.X a) (Q.X b) ≫
        HomologicalComplex.ιTensorObj
          (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
            (.up ℤ)).obj P)
          (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
            (.up ℤ)).obj Q) a b k h :=
      HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
        (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar (spIntegralCondensed l E) f))
        (.up ℤ) P Q a b k h
    rw [reassoc_of% h1, ← Functor.map_comp, ← Functor.map_comp, h2]
  -- Evaluate both composites on the internal pure tensor of `x` and `y`.
  have hk := congrArg (fun g ↦ g.hom.hom.app (op U)
    (ModuleRingedComparison.internalPureTensor (spIntegralCondensed l E) Y
      (P.X a) (Q.X b) (op U) x y)) key
  dsimp only [Functor.comp_obj, Functor.id_obj] at hk
  rw [ModuleRingedComparison.internalModules_comp_apply,
    ModuleRingedComparison.internalModules_comp_apply,
    ModuleRingedComparison.internalModules_comp_apply,
    ModuleRingedComparison.internalModules_comp_apply] at hk
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.mapHomologicalComplex_obj_X] at hk
  rw [ModuleRingedComparison.lowerStar_map_apply,
    ModuleRingedComparison.lowerStar_map_apply] at hk
  have hδ := ModuleRingedComparison.upperStar_δ_unit_internalPureTensor (spIntegralCondensed l E)
    f (P.X a) (Q.X b) U x y
  dsimp only [Functor.comp_obj, Functor.id_obj] at hδ
  rw [hδ] at hk
  rw [tensorGenerator_eq, tensorGenerator_eq, spIntegralModuleEquivalence_map_apply]
  exact hk

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
