/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenCompletedTowerRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestrictionSupplement
public import WeilConjectures.AlgebraicGeometry.ExceptionalDerivedSiteRealization
public import WeilConjectures.AlgebraicGeometry.ExceptionalFiniteSupportRealization
public import WeilConjectures.AlgebraicGeometry.CoefficientSystemDerivedComparison
public import WeilConjectures.AlgebraicGeometry.OpenCompletedRestrictionIdentification
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Site transport and integral realization on a clopen component

Source: blueprint def-pur-section-invariant, finite-clopen expansion, retained steps 8--9;
Zheng, Lemmas 4.10 and 5.22; Stacks Tags 0941 and 08BJ
(blueprint: def-pur-clopen-system-realization-data).

All systems below are actual strict systems. Their scalar forgetting and inverse limit
are the published functors on the derived category of strict towers. The result records
normalization equations for maps, as well as natural isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local irreducible] HasDerivedCategory.standard
set_option allowUnsafeReducibility true
attribute [local reducible] WeilConjectures.IntegralOnSlice.Site
  WeilConjectures.IntegralOnSlice.topology WeilConjectures.IntegralOnSlice.restrict
  WeilConjectures.IntegralOnSlice.ring WeilConjectures.IntegralOnSlice.finite
  WeilConjectures.IntegralOnSlice.projection
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PurityFiniteSetting

-- Since build 2026-10-28 another derived-category instance of the strict levels is in scope here;
-- keep the ones this module was written against.
attribute [local instance 10000] AlgebraicGeometry.strictEtaleSystemDerived
  AlgebraicGeometry.strictEtaleLevelDerived

/-- The transported exceptional functor on all actual derived pro-étale systems,
in the recorded equivalent sequence-site presentation, before reduction or limit.
Source: Zheng 4.10 and 5.22 (blueprint: def-pur-clopen-system-realization-data). -/
def clopenRealizationTransported (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {g : X ⟶ Y} {c : Compactification g}
    (S : StrictEtaleCompactSupport (clopenSystemRing l E) (clopenSystemUniformizer l E) c)
    (G : StrictEtaleExceptionalAdjoint _ _ c S)
    (CX : ClopenSystemComparison l E X S.PX) (CY : ClopenSystemComparison l E Y S.PY) :=
  CY.sequence.derived.inverse ⋙ CY.derived.system.direct ⋙ G.right ⋙
    CX.derived.system.inverse ⋙ CX.sequence.derived.functor

attribute [local instance] OpenCompletedRestriction.ordinaryAdditive
  OpenCompletedRestriction.ordinaryLimits OpenCompletedRestriction.ordinaryColimits
  WeilConjectures.coefficientConstantTowerLimitAdditive
  clopenCompletedTowerAdditive
set_option maxHeartbeats 80000 in
-- Elaborate the normalized comparisons in one result record.
/-- Assertion data for one clopen component: the normalized étale comparison,
its geometric site square, finite evaluations, and its integral functorial image.
These fields are conclusions of the theorem below, never additional hypotheses.
Source: retained steps 8--9 of the section-invariant finite-clopen expansion
(blueprint: def-pur-clopen-system-realization-data). -/
structure ClopenSystemTransportCore (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g] where
  S : StrictEtaleCompactSupport
    (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) c
  G : StrictEtaleExceptionalAdjoint _ _ c S
  Si : StrictEtaleCompactSupport
    (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) (c.precomp j)
  Gi : StrictEtaleExceptionalAdjoint _ _ (c.precomp j) Si
  strict : StrictClopenExceptionalComparison _ _ c j S G Si Gi
  supportNormalization : StrictClopenCompactSupportNormalization _ _ c j S G Si Gi strict
  CX : ClopenSystemComparison P.coefficients.l P.extension X S.PX
  CY : ClopenSystemComparison P.coefficients.l P.extension Y S.PY
  Ci : ClopenSystemComparison P.coefficients.l P.extension Xi Si.PX
  CYi : ClopenSystemComparison P.coefficients.l P.extension Y Si.PY
  coordinatesX : CX.sequence.derived.functor =
    integralExceptionalDerivedCoordinatesInv P.coefficients.l P.extension X
  coordinatesXInv : CX.sequence.derived.inverse =
    integralExceptionalDerivedCoordinates P.coefficients.l P.extension X
  coordinatesY : CY.sequence.derived.inverse =
    integralExceptionalDerivedCoordinates P.coefficients.l P.extension Y
  coordinatesI : Ci.sequence.derived.functor =
    integralExceptionalDerivedCoordinatesInv P.coefficients.l P.extension Xi
  coordinatesYi : CYi.sequence.derived.inverse =
    integralExceptionalDerivedCoordinates P.coefficients.l P.extension Y
  sameDirect : CYi.sequence.derived.inverse ⋙ CYi.derived.system.direct =
    CY.sequence.derived.inverse ⋙ CY.derived.system.direct
  site : ClopenSystemSquare P.coefficients.l P.extension strict CX Ci
  setRestriction : Scheme.ProEtaleObjectRestrictionComparison
    (Scheme.ProEt.mk j) (Type (u + 1))

set_option maxHeartbeats 80000 in
-- Normalize the canonical functor comparisons at the fixed coefficient level.
/-- The whiskered strict-system maps with their normalization equations.
Source: retained finite-clopen step 8
(blueprint: def-pur-clopen-system-realization-data). -/
structure ClopenSystemTransportMaps (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g]
    (C : ClopenSystemTransportCore P c j) where
  transported : C.CY.derived.system.direct ⋙ C.G.right ⋙ C.CX.derived.system.inverse ⋙
      C.site.derived.system.inverse ≅
    C.CY.derived.system.direct ⋙ C.Gi.right ⋙ C.Ci.derived.system.inverse
  transported_map : ∀ L,
    transported.hom.app L =
      C.site.square.hom.app (C.G.right.obj (C.CY.derived.system.direct.obj L)) ≫
        C.Ci.derived.system.inverse.map
          (C.strict.system.comparison.hom.app (C.CY.derived.system.direct.obj L))
  sequenceComparison :
    clopenRealizationTransported P.coefficients.l P.extension C.S C.G C.CX C.CY ⋙
      C.site.sequenceRestriction ≅
    clopenRealizationTransported P.coefficients.l P.extension C.Si C.Gi C.Ci C.CYi
  sequenceComparison_map : sequenceComparison =
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (C.CY.sequence.derived.inverse ⋙ C.CY.derived.system.direct ⋙ C.G.right ⋙
          C.CX.derived.system.inverse) C.CX.sequence.derived.unitIso.symm)
      (C.site.derived.system.inverse ⋙ C.Ci.sequence.derived.functor) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft C.CY.sequence.derived.inverse transported)
      C.Ci.sequence.derived.functor ≪≫
    Functor.isoWhiskerRight (eqToIso C.sameDirect.symm)
      (C.Gi.right ⋙ C.Ci.derived.system.inverse ⋙ C.Ci.sequence.derived.functor)
  system : clopenExceptionalSystem P.coefficients.l P.extension C.S C.G C.CX C.CY ⋙
      C.site.sequenceRestriction ≅
    clopenExceptionalSystem P.coefficients.l P.extension C.Si C.Gi C.Ci C.CYi
  system_sequence : ∀ L,
    system.hom.app L = sequenceComparison.hom.app
      (((sfIntegralConstructible P.coefficients.l P.extension Y).ι ⋙
        (coefficientDerivedSystemEvaluationCalculus.{u, u}
          P.coefficients.l P.extension Y).choose.reduction).obj L)


end WeilConjectures.PurityFiniteSetting
