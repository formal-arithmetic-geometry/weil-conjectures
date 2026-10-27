module

public import Sheaf.Paper.ClopenCanonicalFiniteEvaluation
public import Sheaf.Paper.ClopenSystemRestrictionEvaluation
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
(blueprint: def-pur-clopen-system-finite-realization).

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
-- Normalize the canonical functor comparisons at the fixed coefficient level.
/-- Finite evaluation and canonical counit normalization.
Source: retained finite-clopen step 8
(blueprint: def-pur-clopen-system-finite-realization). -/
structure ClopenSystemTransportFinite (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g]
    (C : ClopenSystemTransportCore P c j) (M : ClopenSystemTransportMaps P c j C) where
  finiteBound : ∀ n (L : (Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y).FullSubcategory),
    ClopenCounitBound (clopenRealizationLevel P n).Ring c L.obj
  finiteBoundI : ∀ n (L : (Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y).FullSubcategory),
    ClopenCounitBound (clopenRealizationLevel P n).Ring (c.precomp j) L.obj
  finiteInsertion : ∀ n,
    Scheme.sfIntrinsicDerivedOpen (clopenRealizationLevel P n).Ring j ⊣
      Scheme.sfIntrinsicDerivedPullback (clopenRealizationLevel P n).Ring j
  finiteInsertion_unit : ∀ n, (finiteInsertion n).unit =
    Scheme.sfIntrinsicDerivedOpenUnit (clopenRealizationLevel P n).Ring j
  finite : ∀ n,
    clopenFiniteInclusion P.coefficients.l P.extension Y n ⋙
        ProEtale.sfFiniteExceptional (clopenRealizationLevel P n).Ring c ⋙
        Scheme.sfIntrinsicDerivedPullback (clopenRealizationLevel P n).Ring j ≅
      clopenFiniteInclusion P.coefficients.l P.extension Y n ⋙
        ProEtale.sfFiniteExceptional (clopenRealizationLevel P n).Ring (c.precomp j)
  finite_counit : ∀ n (L : (Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y).FullSubcategory),
    (Scheme.sfIntrinsicCompactSupport (c.precomp j) (clopenRealizationLevel P n).Ring).map
        ((finite n).hom.app L) ≫
      clopenFiniteCounit (clopenRealizationLevel P n).Ring (c.precomp j) L.obj
        (finiteBoundI n L) =
      ((clopenRealizationLevel P n).clopenSupportComponentComparison c j).inv.app _ ≫
        (Scheme.sfIntrinsicCompactSupport c (clopenRealizationLevel P n).Ring).map
          ((finiteInsertion n).counit.app
            ((ProEtale.sfFiniteExceptional (clopenRealizationLevel P n).Ring c).obj L.obj)) ≫
        clopenFiniteCounit (clopenRealizationLevel P n).Ring c L.obj (finiteBound n L)
  finiteEvaluation : ∀ n,
    clopenRealizationTransported P.coefficients.l P.extension C.S C.G C.CX C.CY ⋙
        coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension X n ≅
      coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Y n ⋙
        ProEtale.sfFiniteExceptional (clopenRealizationLevel P n).Ring c
  finiteEvaluationI : ∀ n,
    clopenRealizationTransported P.coefficients.l P.extension C.Si C.Gi C.Ci C.CYi ⋙
        coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Xi n ≅
      coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Y n ⋙
        ProEtale.sfFiniteExceptional (clopenRealizationLevel P n).Ring (c.precomp j)
  finiteEvaluation_normalized : ∀ n N,
    (finiteEvaluation n).app N = clopenCanonicalFiniteEvaluation P c C.S C.G C.CX C.CY
      C.coordinatesX C.coordinatesY N n
  finiteEvaluationI_normalized : ∀ n N,
    (finiteEvaluationI n).app N = clopenCanonicalFiniteEvaluation P (c.precomp j)
      C.Si C.Gi C.Ci C.CYi C.coordinatesI C.coordinatesYi N n
  restriction : ClopenSystemRestrictionEvaluation P c j C
  finiteEvaluation_map : ∀ n (N : coefficientSequenceDerived.{u, u}
      P.coefficients.l P.extension Y)
      (hN : Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) Y
        ((coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Y n).obj N)),
    (coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Xi n).map
        (M.sequenceComparison.hom.app N) ≫ (finiteEvaluationI n).hom.app N =
      (restriction.evaluation n).hom.app
          ((clopenRealizationTransported P.coefficients.l P.extension C.S C.G C.CX C.CY).obj N) ≫
        (Scheme.sfIntrinsicDerivedPullback (clopenRealizationLevel P n).Ring j).map
          ((finiteEvaluation n).hom.app N) ≫
        (finite n).hom.app ⟨_, hN⟩



end WeilConjectures.PurityFiniteSetting
