/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Ordinary homology of the finite constant tensor model

Source: Stacks Project, sites-cohomology.tex, Tags 094H and 06YU.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-model-homology-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

@[irreducible] private def restrictionCompIso (X : Scheme.{t})
    {R S T : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (α : R ⟶ S) (β : S ⟶ T) :
    SheafOfModules.restrictScalars.{t + 1} (α ≫ β) ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

@[irreducible] private def restrictionIdIso (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    SheafOfModules.restrictScalars.{t + 1} (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

@[irreducible] private def derivedChangeComplexIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ]
    (K : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ) :
    (completedAdicDerivedChange X φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  have := changeIsEquivalence X φ
  let F := completedAdicChange X φ
  let L := completedAdicDerivedChange X φ
  let ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (completedAdicChangeData X φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose
  have : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (completedAdicChangeData X φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose_spec.1
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  let i : L ≅ F.mapDerivedCategory :=
    Functor.leftDerivedNatIso L F.mapDerivedCategory ε F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)
  exact i.app _ ≪≫ F.mapDerivedCategoryFactors.app K

@[irreducible] private def modelHomologyIso (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R) [IsIso φ]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((completedAdicDerivedChange X φ).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P))) ≅
      (finiteCoefficientConstantFunctor X B φ).obj (P.homology q) := by
  have := changeIsEquivalence X φ
  have := (baseConstantExact X B).1
  have := (baseConstantExact X B).2.1
  have := (baseConstantExact X B).2.2
  exact (DerivedCategory.homologyFunctor _ q).mapIso
      (derivedChangeComplexIso X φ (finiteModelConstantComplex X B P)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    ((finiteModelConstantComplex X B P).sc q).mapHomologyIso (completedAdicChange X φ) ≪≫
    (completedAdicChange X φ).mapIso ((P.sc q).mapHomologyIso (baseConstantFunctor X B))

end AlgebraicGeometry.Scheme
