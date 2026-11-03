/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

import WeilConjectures.AlgebraicGeometry.RationalLocalizedHom.NativeContinuousScalarAction
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear

/-! # Native continuous coefficient scalars

Source: sk-prop-sp-rational-adjunction.proof.md, constant-scalar linearity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalLocalizedHom

attribute [local instance 2000] CategoryTheory.Linear.homModule

/-- Native derived right tensoring preserves the canonical continuous scalar action.
Source: sk-prop-sp-rational-adjunction.proof.md, paragraph (1), linearity.
Proof: the nativeContinuousScalarAction comparison identifies the canonical Hom
scalar with the derived action of constant global sections. The ordinary module
category is monoidal linear for this action by monoidalLinearOfRingHom. Its native
derived tensor inherits monoidal linearity. Apply tensorRight's linearity and
rewrite both Hom actions through the comparison. No boundedness, flatness of the
arbitrary derived inputs, or nonemptiness is required.
(blueprint: lem-sp-native-continuous-tensor-scalar). -/
theorem nativeTensorRight_map_smul
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TotallyDisconnectedSpace A]
    (X : Scheme.{u})
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)))
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))}
    (h : K ⟶ L) (a : A) :
    (tensorRight N).map (@SMul.smul A (K ⟶ L) (homModule X A K L).toSMul a h) =
      @SMul.smul A (K ⊗ N ⟶ L ⊗ N)
        (homModule X A (K ⊗ N) (L ⊗ N)).toSMul a ((tensorRight N).map h) := by
  let p := (MonObj.Γ.mapFunctor (upperStarFromPoint X)
    (R := Profinite.continuousMapRingObj A)).comp
      (Profinite.continuousMapConstRingHom A)
  letI := Mod.linearOfRingHom p
  letI := Mod.monoidalLinearOfRingHom p
  rw [nativeContinuousScalarAction X A h a,
    nativeContinuousScalarAction X A ((tensorRight N).map h) a]
  exact Functor.map_smul (tensorRight N) a h

end AlgebraicGeometry.ProEtale.RationalLocalizedHom
