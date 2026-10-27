module

public import Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization
public import Sheaf.Paper.AdicPurityObjects
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.Paper.OpenCompletedRestrictionIdentification
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Site transport and integral realization on a clopen component

Source: blueprint def-pur-section-invariant, finite-clopen expansion, retained steps 8--9;
Zheng, Lemmas 4.10 and 5.22; Stacks Tags 0941 and 08BJ
(blueprint: def-pur-clopen-restriction-evaluation-data).

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
attribute [-instance] WeilConjectures.integralExceptionalEvaluation_additive
attribute [local instance] SheafOfModules.CoefficientSystemOrdinaryImage.inverseAdditive
set_option allowUnsafeReducibility true
attribute [local reducible] WeilConjectures.IntegralOnSlice.Site
  WeilConjectures.IntegralOnSlice.topology WeilConjectures.IntegralOnSlice.restrict
  WeilConjectures.IntegralOnSlice.ring WeilConjectures.IntegralOnSlice.finite
  WeilConjectures.IntegralOnSlice.projection
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PurityFiniteSetting

set_option maxHeartbeats 500000 in
-- Keep the ordinary section and exact localization normalizations in one interface.
/-- The normalized ordinary and derived restriction evaluations. All fields are
assertion data; sections fix the ordinary comparison, and Q fixes its exact descent.
Source: Stacks 00XZ and Zheng 4.10
(blueprint: def-pur-clopen-restriction-evaluation-data). -/
structure ClopenSystemRestrictionEvaluation (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g]
    (C : ClopenSystemTransportCore P c j) where
  ordinary : ClopenSystemOrdinaryRestrictionRealization P c j C
  restrictionDerived : ∀ n, ClopenRestrictionRealizationIso P c j C n
  restrictionDerived_normalized : ∀ n,
    IsClopenRestrictionDerivedNormalized P c j C ordinary n (restrictionDerived n)
  evaluation : ∀ n,
    C.site.sequenceRestriction ⋙
        coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Xi n ≅
      coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension X n ⋙
        Scheme.sfIntrinsicDerivedPullback (clopenRealizationLevel P n).Ring j
  evaluation_normalized : ∀ n N,
    (evaluation n).app N =
      clopenCanonicalRestrictionEvaluation P c j C n (restrictionDerived n) N

end WeilConjectures.PurityFiniteSetting
