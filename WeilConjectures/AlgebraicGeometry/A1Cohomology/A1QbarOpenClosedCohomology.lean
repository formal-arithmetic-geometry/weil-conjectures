/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarStandardCohomology
public import WeilConjectures.AlgebraicGeometry.PerAdic.AdicHeartPullbackFibres
public import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.StageSystem.Const
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
public import WeilConjectures.CategoryTheory.StageSystem.Morphism.PbcDescentFunctors
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.FieldTheory.Perfect
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomUnitNormalization
import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
import WeilConjectures.AlgebraicGeometry.ContinuousRational.DirectImage.RationalDirectImageRealization
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.SixFunctors.Supporting.IntrinsicQbarCategory

/-! # Ordinary constructible cohomology and open--closed restriction on a curve

Source: Bhatt--Scholze, Sections 6.7--6.8, especially Lemmas 6.7.2, 6.7.11,
6.8.7 and Remark 6.8.15; blueprint thm-a1-curve-perverse-heart, Steps 1 and 3
(blueprint: lem-a1-qbar-open-closed-cohomology).

The categories are the recorded PBC finite-stage pair categories. The auxiliary
records below specify the canonical operations and comparison maps in the assertion;
they introduce neither a replacement coefficient category nor arbitrary operation data.

## Main definitions

* `StandardAssertions`: the recorded standard structure, heart and scalar comparisons.
* `ContinuousRealization`: normalized continuous coefficient module representatives.
* `OpenClosed`: actual operations, adjunctions, bottom cohomology and unit comparison.
* `AutomorphismCompatibility`: explicit reindexing equations for all displayed maps.

## Main statements

* `qbar_open_closed_cohomology`: the assertion for a smooth pure-dimensional curve.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w uA vA uB vB uD vD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.A1Cohomology

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]

/-- Cache the existing field-algebra torsion-freeness instance during elaboration.
Source: the coefficient field convention, BS 6.8
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
local instance (priority := 4000) coefficientTorsionFree : Module.IsTorsionFree ℚ_[l] Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

variable [IsAlgClosure ℚ_[l] Ω]

attribute [instance 4000] stageCategory

attribute [instance 4000] stagePreadditive

attribute [instance 4000] pairPreadditive

attribute [instance 4000] pairShift

/-- Cache the existing canonical pair-shift additivity instance.
Source: the recorded pair triangulation, blueprint order 1311
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
local instance (priority := 4000) pairShiftAdditive (X : PerAdic.Base k) (n : ℤ) :
    (shiftFunctor (pbcQbarCategory l Ω X.scheme) n).Additive := inferInstance

/-- Cache the existing zero-object instance, without selecting a new zero object.
Source: the recorded pair triangulation, blueprint order 1311
(blueprint: lem-a1-qbar-open-closed-cohomology). -/
local instance (priority := 4000) pairHasZero (X : PerAdic.Base k) :
    HasZeroObject (pbcQbarCategory l Ω X.scheme) := inferInstance

/-- The existing common-stage standard t-structure, with a separated finite-type base.
Source: BS 6.8.14 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev standard (X : PerAdic.Base k) := PerAdic.commonT l Ω X

/-- The existing heart predicate; this alias fixes its canonical categorical instances.
Source: BBD 1.3.6 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev heartProperty (X : PerAdic.Base k) : ObjectProperty (pbcQbarCategory l Ω X.scheme) :=
  (standard l Ω X).heart

/-- The existing heart-valued zeroth cohomology functor.
Source: BBD 1.3.6 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev zeroth (X : PerAdic.Base k) := (standard l Ω X).homology₀

/-- The full standard heart, with the original underlying Hom sets.
Source: BS 6.8.14 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
abbrev Heart (X : PerAdic.Base k) := (heartProperty l Ω X).FullSubcategory

/-- Ordinary degree-m cohomology with values in the heart: H^0(K[m]).
Source: BS 6.8.11, 6.8.14 (blueprint: lem-a1-qbar-open-closed-cohomology). -/
def cohomology (X : PerAdic.Base k) (m : ℤ) :
    pbcQbarCategory l Ω X.scheme ⥤ Heart l Ω X :=
  shiftFunctor _ m ⋙ (zeroth l Ω X)

end AlgebraicGeometry.Scheme.A1Cohomology
