/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula
import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite site comparison of counits, projections and transposes

Source: blueprint main-20261015, lem-pur-co-smooth-etale-locality, Steps 1 and 3;
Stacks Project, Tags 0B65, 07A4, 0GL1 and 0F7F
(blueprint: lem-pur-finite-site-counit-projection-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local instance 2000] isNoetherian_of_finite
attribute [local irreducible] Etale.derivedTensor derivedTensor
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Etale.projectionMapOfCompactification projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso derivedOpenImmersionLowerShriekProjectionIso
  compactSupportSiteComparison

attribute [local semireducible] Etale.derivedTensor derivedTensor
  Etale.projectionMapOfCompactification projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso derivedOpenImmersionLowerShriekProjectionIso
  compactSupportSiteComparison

attribute [local irreducible] derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
  comparisonOpenTensorIso comparisonOpenDerivedPullbackIso

local syntax (name := startTensorProof) "start_tensor_proof" : tactic
local syntax (name := finishTensorProof) "finish_tensor_proof" : tactic

open Lean Meta Elab Tactic in
open Lean Meta Elab Tactic in
set_option linter.style.multiGoal false in
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- Bounded constructible etale complexes are bounded below.
Source: blueprint finite derived-category convention
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: choose the lower endpoint of the finite cohomological interval in hM.
The defining vanishing outside that interval implies vanishing below its lower endpoint. -/
theorem finiteSiteProjectionInput_plus_source
    (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (_hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M) :
    _root_.DerivedCategory.TStructure.t.plus M := by
  obtain ⟨a, b, _, h⟩ := _hM.2
  exact ⟨a, (_root_.DerivedCategory.isGE_iff M a).2 (fun q hq ↦ h q (.inl hq))⟩

/-- The tensor input in the projection square is bounded below on its stated domain.
Source: blueprint lem-pur-co-smooth-etale-locality, Steps 1 and 3
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: pullback preserves the finite Tor interval of K. Tensoring a bounded complex
M with this pullback has cohomology only in the sum of their two finite intervals.
Thus it is bounded, in particular bounded below. No flatness of A is assumed. -/
theorem finiteSiteProjectionInput_plus
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M)
    (_hK : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K) :
    _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj
        (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K)) := by
  obtain ⟨a, b, _, h⟩ := _hM.2
  have hb : _root_.DerivedCategory.TStructure.t.bounded M :=
    ⟨⟨a, (_root_.DerivedCategory.isGE_iff M a).2 (fun q hq ↦ h q (.inl hq))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff M b).2 (fun q hq ↦ h q (.inr hq))⟩⟩
  obtain ⟨r, s, _, ht⟩ := _hK.2
  exact Etale.plus_derivedTensor_leftDerivedUpperStar f hb
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht)

/-- Comparison preserves the actual proper-mate/open compactification projection.
Source: blueprint lem-pur-co-smooth-etale-locality, Steps 1 and 3;
Stacks Tags 07A4, 0E48 and 0GL1
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: apply ringed tensor/exchange coherence to the proper factor r and the
comparison morphisms. The proper comparison is its direct-image counit mate,
so this identifies the specified proper projections, without an automorphism ambiguity.
Apply comparison_open_tensor_coherence to j and r^*K. Expand both compactification
projections as proper projection, open tensor map, and pullback composition.
Naturality moves the proper comparison past the open map. The open comparison
and monoidal pullback-composition coherence identify the remaining factors.
Their composite is B at M tensor f^*K followed by the specified tensor comparison.
These are precisely proof steps 2 and 3 of the node. -/
theorem finiteSiteCounitProjectionTransport
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f)
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M)
    (hK : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K) :
    D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
        (((Etale.projectionMapOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).app M).app K) ≫
      (compactSupportSiteComparison P.Coefficient c).inv.app
        ⟨_, finiteSiteProjectionInput_plus P f M K hM hK⟩ ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).map
          (comparisonOpenTensorIso P.Coefficient f M K).hom =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient)
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).obj M)).hom.app K ≫
      ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
        ((compactSupportSiteComparison P.Coefficient c).inv.app
          ⟨M, finiteSiteProjectionInput_plus_source P X M hM⟩)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) := by
  exact compact_projection_square P.Coefficient c M K
    (finiteSiteProjectionInput_plus_source P X M hM)
    (finiteSiteProjectionInput_plus P f M K hM hK)

/-- Both specified projections are invertible on the finite-Tor domain used below.
Source: blueprint lem-pur-co-smooth-etale-locality, Step 3; node proof step 4
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: the finite compact projection formula makes the etale component invertible.
The finite Tor interval bounds the proper-factor tensor input after exact open
extension. Apply the existing compactification projection formula by etale comparison
to obtain invertibility of the actual pro-etale component. Only the stated inputs are used. -/
theorem finiteSiteProjections_isIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f)
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M)
    (_hK : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K) :
    IsIso (((Etale.projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app M).app K) ∧
    IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)) := by
  refine ⟨Etale.finiteCompactProjection_etale P.Coefficient c M K, ?_⟩
  have hM := bounded_of_constructible P.Coefficient X M _hM
  obtain ⟨a, b, _, ht⟩ := _hK.2
  have hTor := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht
  have hJ := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} P.Coefficient) c.i).bounded_mapDerivedCategory_obj hM
  have hML := Etale.plus_derivedTensor_leftDerivedUpperStar c.g hJ hTor
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite P.Coefficient c.g
  exact hasProjectionFormulaOfCompactification_of_comparison
    (A := ModuleCat.{u + 1} P.Coefficient) (K₀ := M) (L₀ := K)
    c (Iso.refl _) (Iso.refl _) hM hML inferInstance

end AlgebraicGeometry.ProEtale
