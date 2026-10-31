/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.Pair.FilteredCondensedRepresentingPairData
import all WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.FilteredCondensedCounitFiniteFormula
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SplitCoefficientDerivedFaithfulSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
attribute [local instance 2000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Mod.hasFunctorialFlatResolution
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

@[local instance]
private theorem extension_additive (T : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (constructibleToPadicAlgCl T l E).Additive := by
  have : IsCommMonObj (padicSubfieldRingObj T l E) :=
    isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) T
  have : IsCommMonObj (padicAlgClRingObj T l) :=
    isCommMonObj_condensedRingObj (Profinite.padicAlgClRingObj l) T
  have hi : derivedExtendScalarsToPadicAlgCl T l E ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T l E)).mapDerivedCategory :=
    Functor.leftDerivedFunctorIsoMapDerivedCategory _
  have : (derivedExtendScalarsToPadicAlgCl T l E).Additive :=
    Functor.additive_of_iso hi.symm
  unfold constructibleToPadicAlgCl
  infer_instance

attribute [local irreducible] constructibleExtendScalars constructibleToPadicAlgCl
  CondensedRing.boundedConstructibleLowerShriekOfCompactification
  CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification

set_option maxHeartbeats 2000000 in
-- Converting finite scalar representatives and their zero maps requires extra reduction.
set_option maxHeartbeats 2000000 in
-- The scalar-comparison calculation converts several nested derived functor wrappers.
end WeilConjectures.FilteredCondensedRepresentingPair
