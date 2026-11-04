/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcActualPullProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement

/-! # Derived comparisons on cochain representatives

The canonical derived restriction/pullback comparison is the termwise ordinary comparison
on every complex, and the actual pullback counit on complexes is natural.

Source: Stacks Tags 0D6D and 099N
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits proEtaleRingRestrictionPullbackInv_isIso

section RestrictionPullback

variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)

/-- The inverse derived restriction/pullback comparison is the termwise ordinary comparison
on every complex. Source: Stacks Tag 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem proEtaleRingRestrictionDerivedPullback_inv_fac
    (K : CochainComplex (proEtaleRingModules V SV) ℤ) :
    (proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm).inv.app
        (DerivedCategory.Q.obj K) ≫
      (proEtaleRingRestrictScalars aU).mapDerivedCategory.map
        ((proEtaleRingDerivedPullbackFactors f SV SU cS).hom.app K) ≫
      (proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingModulePullback f SV SU cS).mapHomologicalComplex (.up ℤ)).obj K) =
    (proEtaleRingDerivedPullback f RV RU cR).map
        ((proEtaleRingRestrictScalars aV).mapDerivedCategoryFactors.hom.app K) ≫
      (proEtaleRingDerivedPullbackFactors f RV RU cR).hom.app
        (((proEtaleRingRestrictScalars aV).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm) (.up ℤ)).app K) := by
  have hb : (proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm).inv =
      (Functor.mapDerivedCategoryCompIso (proEtaleRingRestrictScalars aV)
        (proEtaleRingModulePullback f RV RU cR)).inv ≫
      (Functor.mapDerivedCategoryNatIso
        (asIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm))).hom ≫
      (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback f SV SU cS)
        (proEtaleRingRestrictScalars aU)).hom := by
    dsimp [proEtaleRingRestrictionDerivedPullback]
    rw [Category.assoc, ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq]
  rw [hb]
  simp only [proEtaleRingDerivedPullbackFactors, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc, Iso.inv_hom_id_app_assoc]
  rfl

end RestrictionPullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)

/-- The actual pullback counit on cochain representatives is natural.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualPullComplexCounit_naturality
    {P P' : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ} (a : P ⟶ P') :
    (pbcActualDerivedPull g d).map (DerivedCategory.Q.map a) ≫
        pbcActualPullComplexCounit g d P' =
      pbcActualPullComplexCounit g d P ≫
        DerivedCategory.Q.map (((pbcActualModulePull g d).mapHomologicalComplex (.up ℤ)).map a) :=
  (complexCounit (pbcActualModulePull g d) (pbcActualDerivedPull g d)
    (pbcActualPullCounit g d)).naturality a

end AlgebraicGeometry.Scheme
