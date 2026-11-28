/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootLimitCompatibility
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFiniteRootsCanonicalMap
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernHEqCongr
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # The staged form of a local uniformizer reduction
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the same abelian structure on module sheaves as the exact-derived comparison APIs.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

namespace UniformizerChernNormalizationData

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory HasDerivedCategory.standard
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

/-- The completed realization forgets to the same underlying sheaf as forgetting the
completed coefficient action directly. -/
def _root_.AlgebraicGeometry.ProEtale.DiagonalCoefficients.localCompletedForgetIso
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    diagonalCompletedRestriction l T ⋙ diagonalForget l T ≅ localCompletedForget l T :=
  Iso.refl _

/-- The underlying map of the four unit endpoints of a local uniformizer reduction. -/
def localUnitEndpoint (s : UniformizerChernNormalizationData l Y) :
    (localCompletedForget l (ProjectiveLine Y)).obj (SheafOfModules.unit
        (Scheme.purTwistRing (ProjectiveLine Y)
          (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ⟶
      (cartierForget (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).obj
        (geoCartierConstant (ULift.{u + 1} (completedResidue l s.E s.π s.n))
          (ProjectiveLine Y)) :=
  ((s.completedP.underlying ≪≫ localCompletedForgetIso l (ProjectiveLine Y)).inv.app _ ≫
    (Mod.forget _).map s.completedP.unitIso.hom) ≫
    coefficientMap (integralMap l s.E) (ProjectiveLine Y) ≫
    coefficientMap (quotientMap l s.E s.π s.n) (ProjectiveLine Y) ≫
    s.eP.underlying.inv.app (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y))) ≫
    (cartierForget (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).map
      s.eP.unitIso.hom

/-- The underlying map of the four line endpoints of a local uniformizer reduction. -/
def localLineEndpoint (s : UniformizerChernNormalizationData l Y) :
    (localCompletedForget l (ProjectiveLine Y)).obj
        (Scheme.purTwistZlModule (ProjectiveLine Y) l) ⟶
      (cartierForget (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).obj
        (geoCartierLine (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (l ^ (s.n + 1)) s.hA
          (ProjectiveLine Y)) :=
  ((s.completedP.underlying ≪≫ localCompletedForgetIso l (ProjectiveLine Y)).inv.app _ ≫
    (Mod.forget _).map s.completedP.lineIso.hom) ≫
    integralLineMap l s.E (ProjectiveLine Y) ≫
    quotientLineMap l s.E s.π s.n (ProjectiveLine Y) ≫
    s.eP.underlying.inv.app _ ≫
    (cartierForget (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).map
      (s.lineP.iso l).hom

/-- The finite arrow obtained from a completed arrow by the four local coefficient changes,
written stage by stage. -/
abbrev localStagedArrow (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor _ 0).obj
        (geoCartierConstant (ULift.{u + 1} (completedResidue l s.E s.π s.n))
          (ProjectiveLine Y)) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (geoCartierLine (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (l ^ (s.n + 1)) s.hA
          (ProjectiveLine Y)))⟦(2 : ℤ)⟧ :=
  (DerivedCategory.singleFunctor _ 0).map s.eP.unitIso.inv ≫
    SpTowerClasses.mapSingleArrow s.eP.F 2 ((s.scalar.units (ProjectiveLine Y)).iso.inv ≫
      (derivedScalars (quotientMap l s.E s.π s.n) (ProjectiveLine Y)).map
        ((s.toIntegral.units (ProjectiveLine Y)).iso.inv ≫
          (derivedScalars (integralMap l s.E) (ProjectiveLine Y)).map
            ((DerivedCategory.singleFunctor _ 0).map s.completedP.unitIso.inv ≫
              SpTowerClasses.mapSingleArrow s.completedP.F 2 z ≫
              ((DerivedCategory.singleFunctor _ 0).map s.completedP.lineIso.hom)⟦(2 : ℤ)⟧') ≫
          s.toIntegral.lineP.shift (integralMap l s.E)) ≫
      s.scalar.lineP.shift (quotientMap l s.E s.π s.n)) ≫
    ((DerivedCategory.singleFunctor _ 0).map (s.lineP.iso l).hom)⟦(2 : ℤ)⟧'

/-- The local composite is the staged arrow between the explicit finite endpoints. -/
theorem localComposite_eq_staged (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) :
    (finiteUnitComparison (ULift.{u + 1} (completedResidue l s.E s.π s.n))
        (ProjectiveLine Y)).inv ≫ LocalComposite l Y s z ≫
      (finiteLineComparison (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (l ^ (s.n + 1))
        s.hA (ProjectiveLine Y)).hom = localStagedArrow l Y s z := by
  unfold LocalComposite localUnitInv localLine localFunctor ChernCoefficientDiagram.localUnitIso
    QuotientLineRealization.shifted FiniteRealization.shiftedLine CompletedRealization.shiftedLine
    localStagedArrow SpTowerClasses.mapSingleArrow
  apply eq_of_heq
  simp only [id, diagram, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Iso.symm_inv, Functor.comp_map, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]
  heq_congr

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
