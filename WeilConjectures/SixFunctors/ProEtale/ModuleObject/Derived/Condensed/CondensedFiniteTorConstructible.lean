/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeTriangulated

/-! # Intrinsic finite-Tor constructible condensed module objects

Source: latest blueprint sk-def-sf-operations, finite-Tor domain;
(blueprint: def-weil-finite-tor-amplitude).

The existing test by ordinary relative derived tensor against every module in degree
zero applies directly to native module objects. This interface retains the recorded
site presentations and adds their intrinsic ordinary condensed-module specialization.
It does not define the field category by rationalization or by a common-stage model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Bounded constructible objects of finite Tor amplitude in the ordinary derived
category of modules over the pulled-back condensed ring. `finiteTorAmplitude`
tests the actual relative derived tensor with every module placed in degree zero.
The same definition applies to every commutative condensed coefficient ring.
Source: latest blueprint sk-def-sf-operations, finite-Tor domain.
(blueprint: def-weil-finite-tor-amplitude). -/
def condensedConstructibleFiniteTor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
  boundedConstructible (condensedRingObj Λ T) ⊓ _root_.DerivedCategory.finiteTorAmplitude _

/-- The intrinsic full Dctf subcategory; its morphisms are those of the ordinary
module-derived category. No completion or lattice choice enters this definition.
Source: latest blueprint sk-def-sf-operations, finite-Tor domain.
(blueprint: def-weil-finite-tor-amplitude). -/
abbrev CondensedConstructibleFiniteTor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :=
  (condensedConstructibleFiniteTor Λ T).FullSubcategory

end AlgebraicGeometry.ProEtale.CondensedRing
