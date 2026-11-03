/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
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
public import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.Algebra.TrivSqZeroExt.Basic
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
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Geometric inverse images detect bounded constructible condensed complexes

Source: latest blueprint, sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2, final sentence (blueprint: lem-pur-condensed-constructible-point-detection).

All categories here are ordinary derived categories over the actual pulled-back ring object.
The point functor keeps the full small pro-etale site of the algebraically closed field.
The finite-level clause retains the specified etale-origin representative and its maps.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The existing continuous-map condensed commutative ring, bundled with its existing
canonical ring structure. This only packages the published construction.
Source: current blueprint coefficient convention
(blueprint: lem-pur-condensed-constructible-point-detection). -/
noncomputable def continuousMapCoefficient (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  ⟨Profinite.continuousMapRingObj T⟩

set_option maxHeartbeats 2000000 in
-- Elaborating the derived comparison unit in these module-sheaf categories needs more heartbeats.
end AlgebraicGeometry.ProEtale.CondensedRing
