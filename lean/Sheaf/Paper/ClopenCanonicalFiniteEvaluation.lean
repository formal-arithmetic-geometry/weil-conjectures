module

public import Sheaf.Paper.ClopenSystemRealizationData
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
(blueprint: def-pur-clopen-canonical-finite-evaluation).

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

/-- Reuse a recorded geometric comparison in the existing finite-realization interface.
Source: Zheng 4.10 (blueprint: def-pur-clopen-canonical-finite-evaluation). -/
def clopenRealizationComparison (P : PurityFiniteSetting.{u}) (W : Scheme.{u})
    (PX : StrictEtaleEvaluation W (clopenSystemRing P.coefficients.l P.extension)
      (clopenSystemUniformizer P.coefficients.l P.extension))
    (C : ClopenSystemComparison P.coefficients.l P.extension W PX) :
    IntegralExceptionalComparison.{u} P.coefficients.l P.extension W PX where
  ordinary := C.ordinary
  evaluation := C.proEtaleEvaluation
  derived := C.derived

set_option maxHeartbeats 500000 in
-- Elaborate the full canonical composite with its fixed coefficient coordinates.
/-- The finite evaluation map is the composite of the recorded evaluation maps,
scalar-unit coordinate maps, site realization maps and the compact-support adjunction mate.
Source: Zheng 4.10 and 5.22; existing adic finite realization
(blueprint: def-pur-clopen-canonical-finite-evaluation). -/
@[no_expose] def clopenCanonicalFiniteEvaluation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {g : X ⟶ Y} [QuasiCompact g] (c : Compactification g)
    (S : StrictEtaleCompactSupport (clopenSystemRing P.coefficients.l P.extension)
      (clopenSystemUniformizer P.coefficients.l P.extension) c)
    (G : StrictEtaleExceptionalAdjoint _ _ c S)
    (CX : ClopenSystemComparison P.coefficients.l P.extension X S.PX)
    (CY : ClopenSystemComparison P.coefficients.l P.extension Y S.PY)
    (hX : CX.sequence.derived.functor =
      integralExceptionalDerivedCoordinatesInv P.coefficients.l P.extension X)
    (hY : CY.sequence.derived.inverse =
      integralExceptionalDerivedCoordinates P.coefficients.l P.extension Y)
    (N : coefficientSequenceDerived.{u, u} P.coefficients.l P.extension Y) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension X n).obj
        ((clopenRealizationTransported P.coefficients.l P.extension S G CX CY).obj N) ≅
      (ProEtale.sfFiniteExceptional (clopenRealizationLevel P n).Ring c).obj
        ((coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension Y n).obj N) :=
  let BX := clopenRealizationComparison.{u} P X S.PX CX
  let BY := clopenRealizationComparison.{u} P Y S.PY CY
  let RY := (integralExceptionalEtaleRealization.{u} P.coefficients.l P.extension Y n)
    |>.mapDerivedCategory
  let RX := (integralExceptionalEtaleRealization.{u} P.coefficients.l P.extension X n)
    |>.mapDerivedCategory
  let NX := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient) X).mapDerivedCategory
  let DY := (ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient) Y).rightDerivedFunctor
  let H := clopenCounitEtaleRight (clopenRealizationLevel P n).Ring c
  let input := (integralExceptionalDerivedCoordinates P.coefficients.l P.extension Y).obj N
  let A : DerivedCategory.{u + 2} (SheafOfModules.CoefficientSystem.{u + 1, u, u + 1}
    (J := Y.smallEtaleTopology) (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension)) := BY.derived.system.direct.obj input
  let B : DerivedCategory.{u + 2} (SheafOfModules.CoefficientSystem.{u + 1, u, u + 1}
    (J := X.smallEtaleTopology) (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension)) := G.right.obj A
  let V : DerivedCategory.{u + 2}
    (ClopenProEtaleSystem P.coefficients.l P.extension X) :=
    (SheafOfModules.CoefficientSystemDerivedImage.system.{u + 1, u, u + 1, u, u + 1, u + 2}
      BX.derived).inverse.obj B
  let eY := RY.mapIso
    ((SheafOfModules.CoefficientSystemDerivedImage.directEvaluation.{u + 1, u, u + 1,
      u, u + 1, u + 2} BY.derived n).app input) ≪≫
    (integralExceptionalSiteDerivedRight.{u} P.coefficients.l P.extension Y S.PY BY n).app _ ≪≫
    DY.mapIso (integralExceptionalCoordinatesFixed.{u} P.coefficients.l P.extension Y
      CY.proEtaleEvaluation N n)
  let eX :=
    (Scheme.sfIntrinsicDerivedEquivalence X (clopenRealizationLevel P n).Ring).inverse.mapIso
      ((coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension X n).mapIso
        (eqToIso (congrArg (fun e : DerivedCategory.{u + 2}
          (ClopenProEtaleSystem P.coefficients.l P.extension X) ⥤
            coefficientSequenceDerived.{u, u} P.coefficients.l P.extension X ↦ e.obj V) hX))) ≪≫
    integralExceptionalCoordinatesInvFixed.{u} P.coefficients.l P.extension X
      CX.proEtaleEvaluation V n ≪≫
    (integralExceptionalProRealization.{u} P.coefficients.l P.extension X
      n).mapDerivedCategory.mapIso
      ((SheafOfModules.CoefficientSystemDerivedImage.inverseEvaluation.{u + 1, u, u + 1,
        u, u + 1, u + 2} BX.derived n).app B) ≪≫
    (integralExceptionalSiteDerivedInverse.{u} P.coefficients.l P.extension X S.PX BX n).app _ ≪≫
    NX.mapIso (RX.mapIso ((G.evaluation n).app A) ≪≫
      (integralExceptionalEtaleRightAdjoint.{u} P.coefficients.l P.extension g c S n G H
        (clopenCounitEtaleAdjunction (clopenRealizationLevel P n).Ring c)).app _ ≪≫
      H.mapIso eY)
  (coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l P.extension X n).mapIso
    (eqToIso (congrArg (fun e : coefficientSequenceDerived.{u, u}
      P.coefficients.l P.extension Y ⥤ DerivedCategory.{u + 2}
      (ClopenProEtaleSystem P.coefficients.l P.extension Y) ↦
      CX.sequence.derived.functor.obj (CX.derived.system.inverse.obj
        (G.right.obj (CY.derived.system.direct.obj (e.obj N))))) hY)) ≪≫
  (Scheme.sfIntrinsicDerivedEquivalence X (clopenRealizationLevel P n).Ring).counitIso.symm.app _ ≪≫
    (Scheme.sfIntrinsicDerivedEquivalence X (clopenRealizationLevel P n).Ring).functor.mapIso eX


end WeilConjectures.PurityFiniteSetting
