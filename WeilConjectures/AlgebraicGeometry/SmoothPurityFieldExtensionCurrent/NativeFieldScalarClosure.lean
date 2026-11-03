/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityFieldExtensionCurrent.FieldExtensionDefinitions
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
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
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorShriek
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.MapModScalarExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
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
import WeilConjectures.CategoryTheory.SixFunctors.WeakSerreBoundedThick
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # Native bounded constructibility under finite field scalar extension

Source: sk-lem-sp-field-extension-towers, finite-free coefficient extension,
and sk-prop-scalar-six, constructible preservation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open AlgebraicGeometry.ProEtale.SmoothPurityRationalCurrent
open AlgebraicGeometry.ProEtale.SmoothPurityFieldExtensionCurrent
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SmoothPurityFieldExtensionCurrent

/-- A finite continuous field extension preserves native bounded constructibility
on every scheme, including schemes without a Noetherian hypothesis.
Source: sk-lem-sp-field-extension-towers, finite-free scalar extension
(blueprint: lem-pur-native-field-scalar-closure).

Proof. The continuous finite field extension is internally finite free, so its
extension functor is exact. Its total left derivation agrees with the induced
functor on derived categories. Exactness preserves cohomological bounds and
identifies the target homology with scalar extension of the source homology.
Finite constant presentations extend by the balanced scalar functor; pullback
commutes with scalar extension on every stratum and every constant local cover.
Thus all homology objects retain finite constant local models. Transport along
the derived comparison gives the stated native predicate. -/
theorem nativeFieldScalarClosed (ell : ℕ) [Fact ell.Prime]
    (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
    (T : Scheme.{u}) (K : BC ell (.rational E) T) :
    constantModelBoundedConstructible ((Coefficient.rational F).obj ell) T
      ((scalarSixChange (inclusion ell h) T).obj K.obj) := by
  let G := Mod.extendScalars (padicSubfieldRingObjMap T ell h)
  let e := G.leftDerivedFunctorIsoMapDerivedCategory
  have hi := (constantModelConstructibleFiniteTor_wellDefined
    ((Coefficient.rational F).obj ell) T).1
  let P : ObjectProperty _ :=
    IsConstantModelConstructible ((Coefficient.rational F).obj ell) T
  let : P.IsClosedUnderIsomorphisms := hi
  refine ⟨?_, fun n ↦ ?_⟩
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso (e.app K.obj).symm
      (G.bounded_mapDerivedCategory_obj K.property.1)
  · exact P.prop_of_iso
      ((G.mapDerivedCategoryHomologyFunctorIso n).app K.obj ≪≫
        ((DerivedCategory.homologyFunctor _ n).mapIso (e.app K.obj)).symm)
      (constant_model_scalar_extension (Profinite.padicSubfieldRingObjMap ell h) T
        ((DerivedCategory.homologyFunctor _ n).obj K.obj) (K.property.2 n))

end AlgebraicGeometry.ProEtale.SmoothPurityFieldExtensionCurrent
