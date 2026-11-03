/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
import WeilConjectures.AlgebraicGeometry.DualBundlePairing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Fourier–Deligne stalk at the origin

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-c-dl-a1-hc1/lem-fd-stalk-at-origin.md and its proof
(blueprint: lem-fd-stalk-at-origin).

All complexes and direct images below are ordinary condensed coefficient modules.
The two cohomology identifications concern the ordinary middle image shifted by one;
the arbitrary Weil-complex assertion is instead an isomorphism of derived stalks.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing WeilConjectures WeilConjectures.NativeL2
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.CondensedOrigin

/-- The finite-field affine-line model, with its actual structure morphism.
Source: the affine line in the statement (blueprint: lem-fd-stalk-at-origin). -/
abbrev model (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) :=
  Over.mk (AffineSpace PUnit (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))

/-- The canonical base-change identification of the geometric model with the affine line.
Source: the geometric fibre in proof paragraph 1 (blueprint: lem-fd-stalk-at-origin). -/
def lineIso (D : FiniteFieldDatum.{u}) :
    AffineSpace PUnit (Spec (.of D.k)) ≅ (D.geometricFiber (model D)).left :=
  (AffineSpace.isPullback_map (n := PUnit)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).isoPullback

set_option maxHeartbeats 2000000 in
-- Derived coefficient functors carry large explicit module-category instance terms.
/-- The geometric origin stalk, evaluated as a derived coefficient module.
Source: the left side of the displayed origin formula
(blueprint: lem-fd-stalk-at-origin). -/
@[irreducible] def originStalk (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    DerivedCategory (NativeCondensedModule.Modules ℓ (AffineSpace PUnit (Spec (.of D.k)))) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ))) :=
  moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of D.k))) ⋙
    (condensedRingCoefficientSections (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of D.k))).rightDerivedFunctor

set_option maxHeartbeats 2000000 in
-- Derived coefficient functors carry large explicit module-category instance terms.
set_option maxHeartbeats 2000000 in
-- Derived coefficient functors carry large explicit module-category instance terms.
set_option maxHeartbeats 2000000 in
-- Derived coefficient functors carry large explicit module-category instance terms.
end AlgebraicGeometry.CondensedOrigin
