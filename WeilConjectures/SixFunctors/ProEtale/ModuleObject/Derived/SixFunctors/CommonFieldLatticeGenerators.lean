/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # Common finite coefficient fields for lattice generators

Source: blueprint main-20261015, proper base change, rational proof, paragraph (3)
(blueprint: lem-sfb-common-field-lattice-generators).

The helper definitions only specialize existing coefficient objects and functors.
The final comparison is characterized after restriction to the locally closed stratum;
its normalization uses the actual derived counit and scalar-tower isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The existing condensed ring of integers, bundled for scalar change.
Source: rational proper-base-change proof (3)
(blueprint: lem-sfb-common-field-lattice-generators). -/
abbrev latticeIntegralRing (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) : ScalarSixRing.{u} :=
  ⟨Profinite.padicIntegersRingObj ell E.1⟩

/-- The existing finite-subextension-valued algebraic closure coefficient ring.
Source: rational proper-base-change proof (3)
(blueprint: lem-sfb-common-field-lattice-generators). -/
abbrev latticeClosureRing (ell : ℕ) [Fact ell.Prime] : ScalarSixRing.{u} :=
  ⟨Profinite.padicAlgClRingObj ell⟩

/-- Postcomposition by the inclusion of valuation subrings. This uses the valuation
inherited from the fixed algebraic closure, not a newly chosen absolute value.
Source: rational proper-base-change proof (3), common coefficient field
(blueprint: lem-sfb-common-field-lattice-generators). -/
def latticeIntegerInclusion (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    PadicAlgCl.integers ell E.1 →+* PadicAlgCl.integers ell F.1 :=
  letI : Algebra E.1 F.1 := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower E.1 F.1 (PadicAlgCl ell) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  PadicAlgCl.integersMap ell E.1 F.1

/-- The continuous-function condensed-ring map induced by inclusion of integers.
Source: rational proper-base-change proof (3), coefficient tower
(blueprint: lem-sfb-common-field-lattice-generators). -/
def latticeIntegralMap (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    latticeIntegralRing.{u} ell E ⟶ latticeIntegralRing ell F :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (latticeIntegerInclusion ell h)
        (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _))⟩⟩

open MonoidalCategory MonObj in
end AlgebraicGeometry.ProEtale.CondensedRing
