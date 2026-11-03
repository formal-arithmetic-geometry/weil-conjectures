/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.FixedModuleGeometricStalkFunctors
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Nilpotent.Defs

import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor
import WeilConjectures.AlgebraicGeometry.FixedModuleGeometricStalkFunctors
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTorTest
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic

/-! # Compact cohomology and geometric stalks with internal finite coefficients

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-lem-tf-compact-trace/det-compact-trace-point-objects.md and its proof
(blueprint: det-compact-trace-point-objects).

The complex and its compactly supported direct image remain in the categories of
internal modules over the pulled-back condensed coefficient ring. Only the stalk
is passed through the normalized ordinary coefficient equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The geometric stalk of an internal finite-discrete coefficient complex, valued in
ordinary A-modules. First use the existing normalized section-action equivalence;
then apply the derived recorded fixed-module pro-etale stalk, with scalar restriction
along A ≃ ULift A. The stalk functor is exact, so its total right derived functor
is its termwise extension. Choosing an Encoding does not choose an arbitrary functor:
its ring map is fixed on constant scalars, and its two forward functors are the specified
section-action and scalar-restriction functors. The existence theorem is already proved.

Source: the item's DAG proof, step 3; Stacks Tags 0993 and 03CY
(blueprint: det-compact-trace-point-objects). -/
def internalFiniteDiscreteDerivedStalk
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    _root_.DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X)) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} A) :=
  (Classical.choice (FiniteDiscreteOrdinary.encoding_exists A X)).fixedDerived.functor ⋙
    (fixedModuleGeometricStalkFunctor (ULift.{u + 1} A) x ⋙
      ModuleCat.restrictScalars
        (ULift.ringEquiv.symm.toRingHom : A →+* ULift.{u + 1} A)).rightDerivedFunctor

/-- Canonical scalar-universe transport for the ordinary stalk complex.
This is the actual termwise derived equivalence induced by ULift A ≃ A. It keeps
all underlying module elements and all test modules, while placing the ring in
Mathlib's tensor universe.
Source: the coefficient convention in the item's stalk assertion; Stacks Tag 0651
(blueprint: det-compact-trace-point-objects). -/
def internalFiniteDiscreteStalkScalarLift (A : Type u) [CommRing A] :
    _root_.DerivedCategory (ModuleCat.{u + 1} A) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  let e : ModuleCat.{u + 1} A ≌ ModuleCat.{u + 1} (ULift.{u + 1} A) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A)
  e.mapDerivedCategory.functor

end AlgebraicGeometry.ProEtale
