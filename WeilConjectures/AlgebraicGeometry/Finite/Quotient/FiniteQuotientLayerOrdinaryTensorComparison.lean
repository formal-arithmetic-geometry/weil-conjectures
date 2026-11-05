/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels

public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientPreviousLocalComplexesChartHomology
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelResidueComparison
import WeilConjectures.AlgebraicGeometry.Constant.ConstantRealizationScalarRestriction
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientConstantTensorComparison

/-! # Ordinary constant tensor compatibility for the finite coefficient layer

Source: Stacks Project, Tags 03EK, 03EL and 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-ordinary-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t uC vC uD vD uE vE uH vH
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

open MonoidalCategory
open scoped TensorProduct
attribute [local instance] ULift.algebra'
attribute [local irreducible] completedAdicChangeData
  SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

@[irreducible] private def layerCoefficientRestriction (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
    [IsIso φB] [IsIso φD] (f : B →+* D) (ψ : R ⟶ S)
    (h : adicConstantMap X f ≫ φD = φB ≫ ψ) :
    finiteCoefficientConstantFunctor X D φD ⋙ SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ) ≅
      ModuleCat.restrictScalars f ⋙ finiteCoefficientConstantFunctor X B φB := by
  let H := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})
  let G := SheafOfModules.restrictScalars.{t + 1} (H.map φB)
  have : G.IsEquivalence := restrictionIsEquivalence X (H.mapIso (asIso φB))
  have hh : H.map φB ≫ H.map ψ = adicModuleMap X f ≫ H.map φD := by
    change H.map φB ≫ H.map ψ = H.map (adicConstantMap X f) ≫ H.map φD
    rw [← H.map_comp, ← H.map_comp, h]
  let e : finiteCoefficientConstantFunctor X D φD ⋙
        SheafOfModules.restrictScalars (H.map ψ) ⋙ G ≅
      ModuleCat.restrictScalars f ⋙ finiteCoefficientConstantFunctor X B φB ⋙ G :=
    Functor.isoWhiskerLeft (finiteCoefficientConstantFunctor X D φD)
        (restrictionCompIso X (H.map φB) (H.map ψ)).symm ≪≫
      Functor.isoWhiskerLeft (finiteCoefficientConstantFunctor X D φD)
        (eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) hh)) ≪≫
      Functor.isoWhiskerLeft (finiteCoefficientConstantFunctor X D φD)
        (restrictionCompIso X (adicModuleMap X f) (H.map φD)) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (baseConstantFunctor X D) (changeUnitIso X φD).symm)
        (SheafOfModules.restrictScalars (adicModuleMap X f)) ≪≫
      (constantRealization_restrictScalars X f).some.symm ≪≫
      Functor.isoWhiskerLeft (ModuleCat.restrictScalars f ⋙ baseConstantFunctor X B)
        (changeUnitIso X φB)
  exact Functor.fullyFaithfulCancelRight G e

end AlgebraicGeometry.Scheme
