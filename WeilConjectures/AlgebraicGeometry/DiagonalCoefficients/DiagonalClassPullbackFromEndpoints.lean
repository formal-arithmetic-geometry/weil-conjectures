/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassPullbackFrame
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalLimitBoundaryNaturality
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCompletedArrowTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSupportedEndpointTransport

/-! # Assembly of completed diagonal pullback from its two endpoints
Source: blueprint coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource
  SpTowerClasses.mapSingleArrow derivedUpper singlePullback PullEndpoint.shift

set_option maxHeartbeats 500000 in
-- Check the concrete realization application separately from the limit chase.
/-- Realize the completed square using its two prescribed endpoint equations.
Proof: apply the categorical single-arrow realization theorem with the actual
single pullback and ordinary supported map. -/
private theorem classSquare_realize (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (d : ClassLimitPresentation l Y hY D) (d' : ClassLimitPresentation l Y' hY' D')
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (e : CompletedRealization l (diagonalSurface Y))
    (e' : CompletedRealization l (diagonalSurface Y'))
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (a : DiagonalClassSourceEndpoint (g := g) (d := d) (d' := d') s s')
    (b : DiagonalClassLineEndpoint a.frame)
    (hcompleted : (diagonalRealizationPull l (baseW g)).mapDerivedCategory.map δ ≫
        a.frame.lineComparison.hom = (a.frame.sourceComparison s s').hom ≫ δ') :
    let R := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let δz := (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).map s.inv ≫
      SpTowerClasses.mapSingleArrow e.F (2 : ℤ) δ ≫
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).map
          e.lineIso.hom)⟦(2 : ℤ)⟧'
    let δz' := (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map s'.inv ≫
      SpTowerClasses.mapSingleArrow e'.F (2 : ℤ) δ' ≫
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          e'.lineIso.hom)⟦(2 : ℤ)⟧'
    ∃ data : SourcePullback R g (zlLine l)
        (spIntegralComparison (baseP g) l (bottomField l))
        (spIntegralComparison (baseW g) l (bottomField l)),
      (derivedUpper R (baseW g)).map δz ≫ data.endpoints.lineW.shift =
        (singlePullback R (baseW g) (source R Y)).hom ≫
          (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
            data.supported.hom ≫ δz' := by
  refine ⟨a.frame.data, ?_⟩
  exact diagonalCompletedSingleArrow_realize a.frame.realizationComparison
    (2 : ℤ) s e.lineIso s' e'.lineIso
    (a.frame.sourceComparison s s') a.frame.lineComparison
    (singlePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)
      (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y))
    a.frame.data.supported a.frame.data.endpoints.lineW.shift
    a.realization_endpoint b.realization_endpoint δ δ' hcompleted


set_option maxHeartbeats 500000 in
-- The concrete derived comparisons require substantial kernel conversion work.
/-- The entire boundary square and its normalized source and line endpoints
imply the completed class pullback equation.

Source: blueprint coefficient changes (3), whole-system naturality and realization.
(blueprint: lem-diagonal-class-pullback-from-endpoints).

Proof: apply naturality of the full limit comparison to the boundary square in
strict systems. Substitute its two endpoint equations and cancel the invertible
new target comparison. The uniqueness assertion for the new completed limit
identifies the conjugated pulled arrow. Naturality of the realization comparison
and its two endpoint equations then give the displayed condensed equation.
No equality is detected by finite evaluations. -/
theorem diagonalClassPullback_from_endpoints (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (d : ClassLimitPresentation l Y hY D) (d' : ClassLimitPresentation l Y' hY' D')
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (hδ : (diagonalCompletedUnderlying l (diagonalSurface Y)).map δ ≫ d.targetMap =
      d.sourceMap ≫ d.L.R.map (D.T.map (diagonalIntegralBoundary Y).hom))
    (hδ' : (diagonalCompletedUnderlying l (diagonalSurface Y')).map δ' ≫ d'.targetMap =
      d'.sourceMap ≫ d'.L.R.map (D'.T.map (diagonalIntegralBoundary Y').hom))
    (e : CompletedRealization l (diagonalSurface Y))
    (e' : CompletedRealization l (diagonalSurface Y'))
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (a : DiagonalClassSourceEndpoint (g := g) (d := d) (d' := d') s s')
    (b : DiagonalClassLineEndpoint a.frame) :
    let R := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let δz := (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).map s.inv ≫
      SpTowerClasses.mapSingleArrow e.F (2 : ℤ) δ ≫
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).map
          e.lineIso.hom)⟦(2 : ℤ)⟧'
    let δz' := (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map s'.inv ≫
      SpTowerClasses.mapSingleArrow e'.F (2 : ℤ) δ' ≫
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          e'.lineIso.hom)⟦(2 : ℤ)⟧'
    ∃ data : SourcePullback R g (zlLine l)
        (spIntegralComparison (baseP g) l (bottomField l))
        (spIntegralComparison (baseW g) l (bottomField l)),
      (derivedUpper R (baseW g)).map δz ≫ data.endpoints.lineW.shift =
        (singlePullback R (baseW g) (source R Y)).hom ≫
          (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
            data.supported.hom ≫ δz' := by
  have hrestricted :
      (diagonalClassPull l (baseW g)).mapDerivedCategory.map
          ((diagonalCompletedUnderlying l (diagonalSurface Y)).map δ) ≫
        (a.frame.scalarComparison.hom.app (diagonalCompletedCodomain l Y) ≫
          (diagonalCompletedUnderlying l (diagonalSurface Y')).map a.frame.lineComparison.hom) =
      (a.frame.scalarComparison.hom.app (diagonalCompletedDomain l Y) ≫
          (diagonalCompletedUnderlying l (diagonalSurface Y')).map
            (a.frame.sourceComparison s s').hom) ≫
        (diagonalCompletedUnderlying l (diagonalSurface Y')).map δ' := by
    exact diagonalLimitBoundary_naturality d.L.R d'.L.R
      (diagonalClassTowerPull l (baseW g)).mapDerivedCategory
      (diagonalClassPull l (baseW g)).mapDerivedCategory a.frame.limitComparison
      (D.T.map (diagonalIntegralBoundary Y).hom)
      (D'.T.map (diagonalIntegralBoundary Y').hom)
      a.frame.systemSource a.frame.systemTarget a.frame.boundary
      d.sourceMap d.targetMap d'.sourceMap d'.targetMap
      ((diagonalCompletedUnderlying l (diagonalSurface Y)).map δ)
      ((diagonalCompletedUnderlying l (diagonalSurface Y')).map δ') hδ hδ' _ _
      (by simpa only [Category.assoc, Nat.cast_one, Nat.cast_ofNat] using! a.limit_endpoint)
      (by simpa only [Category.assoc, Nat.cast_one, Nat.cast_ofNat] using! b.limit_endpoint)
  have hcompleted : (diagonalRealizationPull l (baseW g)).mapDerivedCategory.map δ ≫
      a.frame.lineComparison.hom = (a.frame.sourceComparison s s').hom ≫ δ' := by
    apply diagonalCompletedArrow_of_restricted_square
      (diagonalCompletedUnderlying l (diagonalSurface Y))
      (diagonalCompletedUnderlying l (diagonalSurface Y'))
      (diagonalRealizationPull l (baseW g)).mapDerivedCategory
      (diagonalClassPull l (baseW g)).mapDerivedCategory
      a.frame.scalarComparison (a.frame.sourceComparison s s') a.frame.lineComparison
      δ δ' hrestricted
    intro z hz
    exact d'.eq_of_map_eq l Y' hY' D' δ' hδ' z hz
  exact classSquare_realize l g hY hY' D D' d d' δ δ' e e' s s' a b hcompleted

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
