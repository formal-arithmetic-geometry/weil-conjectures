/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenSystemRealizationData
public import WeilConjectures.AlgebraicGeometry.AdicPurityObjects
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
(blueprint: def-pur-clopen-canonical-restriction-evaluation).

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

/-- The type of the actual level restriction realization, with all site sizes fixed.
Source: Stacks 00XZ; Zheng 4.10
(blueprint: def-pur-clopen-canonical-restriction-evaluation). -/
abbrev ClopenRestrictionRealizationIso (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g]
    (C : ClopenSystemTransportCore P c j) (n : ℕ) :=
  (C.site.derived.level n).inverse ⋙
        (integralExceptionalProRealization P.coefficients.l P.extension Xi
      n).mapDerivedCategory ≅
      (integralExceptionalProRealization P.coefficients.l P.extension X
      n).mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient)
        j).mapDerivedCategory

set_option maxHeartbeats 500000 in
-- Elaborate the full canonical composite with its fixed coefficient coordinates.
/-- The evaluated open restriction, transported through the normalized fixed coefficients.
The supplied level map is normalized on ordinary complexes in the finite-data record.
Source: Stacks 00XZ and Zheng 4.10
(blueprint: def-pur-clopen-canonical-restriction-evaluation). -/
@[no_expose] def clopenCanonicalRestrictionEvaluation (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g]
    (C : ClopenSystemTransportCore P c j) (n : ℕ)
    (r : ClopenRestrictionRealizationIso P c j C n)
    (N : coefficientSequenceDerived.{u, u} P.coefficients.l P.extension X) :
    (coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Xi n).obj
        (C.site.sequenceRestriction.obj N) ≅
      (finiteDerivedPullback P.coefficients.l P.extension n j).obj
        ((coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension X n).obj N) :=
  let input := (integralExceptionalDerivedCoordinates P.coefficients.l P.extension X).obj N
  let B := (SheafOfModules.CoefficientSystemDerivedImage.system.{u + 1, u, u + 1,
    u, u + 1, u + 2} C.site.derived).inverse.obj input
  let U := (ProEtale.upperStar
    (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient) j).mapDerivedCategory
  let eIn := integralExceptionalCoordinatesFixed P.coefficients.l P.extension X
    C.CX.proEtaleEvaluation N n
  let eOut :=
    (Scheme.sfIntrinsicDerivedEquivalence Xi
    (clopenRealizationLevel P n).Ring).inverse.mapIso
      ((coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Xi n).mapIso
        (eqToIso (congrArg (fun e : DerivedCategory.{u + 2}
          (ClopenProEtaleSystem P.coefficients.l P.extension Xi) ⥤
          coefficientSequenceDerived.{u, u} P.coefficients.l P.extension Xi ↦ e.obj B)
            C.coordinatesI))) ≪≫
    integralExceptionalCoordinatesInvFixed P.coefficients.l P.extension Xi
      C.Ci.proEtaleEvaluation B n ≪≫
    (integralExceptionalProRealization P.coefficients.l P.extension Xi
      n).mapDerivedCategory.mapIso
      ((SheafOfModules.CoefficientSystemDerivedImage.inverseEvaluation.{u + 1, u, u + 1,
        u, u + 1, u + 2} C.site.derived n).app input) ≪≫
    r.app _ ≪≫ U.mapIso eIn
  (coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Xi n).mapIso
    (eqToIso (congrArg (fun e : coefficientSequenceDerived.{u, u}
      P.coefficients.l P.extension X ⥤ DerivedCategory.{u + 2}
      (ClopenProEtaleSystem P.coefficients.l P.extension X) ↦
      C.Ci.sequence.derived.functor.obj (C.site.derived.system.inverse.obj (e.obj N)))
        C.coordinatesXInv)) ≪≫
  (Scheme.sfIntrinsicDerivedEquivalence Xi
    (clopenRealizationLevel P n).Ring).counitIso.symm.app _ ≪≫
    (Scheme.sfIntrinsicDerivedEquivalence Xi
    (clopenRealizationLevel P n).Ring).functor.mapIso eOut ≪≫
    (purAdicFinitePullbackPresentation P.coefficients.l P.extension j n).symm.app _


end WeilConjectures.PurityFiniteSetting
