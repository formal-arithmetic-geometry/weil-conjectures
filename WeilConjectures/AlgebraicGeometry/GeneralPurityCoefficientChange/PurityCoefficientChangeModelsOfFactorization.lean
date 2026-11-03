/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityCoefficientChange.PurityCoefficientChangeData
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DerivedConstructibleLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.Compactification.NagataCompactification
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.SmoothPurity.ComplexColimitHomotopyColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import Mathlib.CategoryTheory.Linear.Yoneda
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
import WeilConjectures.CategoryTheory.HomColimitExtension
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.CompletePartialOrder
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import WeilConjectures.SixFunctors.TopologicalLisseIntegralClosure
import WeilConjectures.SixFunctors.TopologicalIntegralConstructibility
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc

/-! # Integral models transported through a coefficient automorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange

attribute [local irreducible] scalarSixChange instCategoryDerivedCategory
  MorphismProperty.instCategoryLocalization DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarSixTower scalarChangeUnit

set_option maxHeartbeats 400000 in
-- Scalar tower and full-subcategory presentations require additional elaboration.
set_option maxRecDepth 2048 in
/-- A factorization through canonical localization and a field coefficient
isomorphism supplies integral models.
Source: coefficient-change clause (2), independence of coefficient presentation
(blueprint: lem-pur-coefficient-models-of-factorization).
Proof: change the rational object by the inverse coefficient automorphism, which
preserves the native constructible finite-Tor subcategory. Choose its canonical
integral model. Extend that model through the coefficient automorphism. The scalar
associator identifies this with extension by the proposed coefficient map. The
associator for the inverse followed by the automorphism, and the scalar unitor,
identify the resulting object with the original rational object. -/
theorem rational_models_of_factorization (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (a : (Coefficient.integral E).bundled.{u} ell ⟶ (Coefficient.rational E).bundled ell)
    (σ : (Coefficient.rational E).bundled.{u} ell ≅ (Coefficient.rational E).bundled ell)
    (hσ : a = scalarSixIntegralToField ell E ≫ σ.hom)
    (K : (Coefficient.rational E).ctf ell X.left) :
    ∃ K₀ : (Coefficient.integral E).ctf ell X.left,
      Nonempty ((scalarSixChange a X.left).obj K₀.obj ≅ K.obj) := by
  subst a
  have hid : IsListedScalarCoefficientMap ell
      (𝟙 ((Coefficient.rational E).bundled.{u} ell)) := by
    exact .field (le_refl E)
  have hi : ListedScalarChange ell σ.inv := .ofListed (by
    simpa [Iso.refl_hom] using
      IsListedScalarCoefficientMap.iso (Iso.refl _) σ.symm hid)
  let K' : (Coefficient.rational E).ctf ell X.left :=
    ⟨(scalarSixChange σ.inv X.left).obj K.obj, listedScalarChangeCtf ell k hi X K⟩
  obtain ⟨K₀, ⟨e⟩⟩ := canonical_rational_models ell k X E K'
  let eσ : scalarSixChange σ.inv X.left ⋙ scalarSixChange σ.hom X.left ≅
      𝟭 ((Coefficient.rational E).derived ell X.left) :=
    scalarSixTower σ.inv σ.hom X.left ≪≫
      eqToIso (congrArg (fun b ↦ scalarSixChange b X.left) σ.inv_hom_id) ≪≫
      scalarChangeUnit ((Coefficient.rational E).bundled ell) X.left
  let e₁ : (scalarSixChange (scalarSixIntegralToField ell E ≫ σ.hom) X.left).obj K₀.obj ≅
      (scalarSixChange σ.hom X.left).obj
        ((scalarSixChange (scalarSixIntegralToField ell E) X.left).obj K₀.obj) :=
    (scalarSixTower (scalarSixIntegralToField ell E) σ.hom X.left).symm.app K₀.obj
  let e₂ := (scalarSixChange σ.hom X.left).mapIso e
  let e₃ : (scalarSixChange σ.hom X.left).obj
      ((scalarSixChange σ.inv X.left).obj K.obj) ≅ K.obj := eσ.app K.obj
  exact ⟨K₀, ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩⟩

end AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange
