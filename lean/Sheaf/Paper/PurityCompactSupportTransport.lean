/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.PurityTateDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison

/-! # Compact-support transport of strict Weil data

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
`def-pur-compact-support-transport` (blueprint: def-pur-compact-support-transport).

The finite construction uses the ambient ringed mate and canonical open base change.
The integral construction uses the specified completed exchange. At higher stages the
same ordered composite uses the supplied domains and comparisons of def-exchange-projection.
The scheme-Frobenius form precomposes the datum with kappa, including for Rf_! M.
No preservation or invertibility assertion is included.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u uX uB uY uB' vX vB vY vB' uC vC uD vD

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures.Purity

/-- The finite compactification exchange is the ambient ringed exchange on j_! M,
followed by proper direct image of the canonical open base-change comparison.
The constant coefficient identifications agree by their constant-section normalization.
Source: the finite-coefficient formula in the blueprint
(blueprint: def-pur-compact-support-transport). -/
def finiteCompactSupportTransportExchange
    (P : PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : IsPullback g' c'.i c.i gbar)
    (M : proEtaleDerivedCategory X P.Ring) :
    (proEtaleConstantRingDerivedPullback P.Ring g).obj
        ((proEtaleRingDerivedDirectImage c.g
          (proEtaleConstantRing Y P.Ring) (proEtaleConstantRing c.Z P.Ring)
          (proEtaleConstantRingComparison c.g P.Ring)).obj
            ((sfIntrinsicDerivedOpen P.Ring c.i).obj M)) ⟶
      (proEtaleRingDerivedDirectImage c'.g
        (proEtaleConstantRing Y' P.Ring) (proEtaleConstantRing c'.Z P.Ring)
        (proEtaleConstantRingComparison c'.g P.Ring)).obj
          ((sfIntrinsicDerivedOpen P.Ring c'.i).obj
            ((proEtaleConstantRingDerivedPullback P.Ring g').obj M)) := by
  let hcoeff : HEq
      (proEtaleRingCompositeCoefficients gbar c.g
        (proEtaleConstantRing Y P.Ring) (proEtaleConstantRing c.Z P.Ring)
        (proEtaleConstantRing c'.Z P.Ring)
        (proEtaleConstantRingComparison c.g P.Ring)
        (proEtaleConstantRingComparison gbar P.Ring))
      (proEtaleRingCompositeCoefficients c'.g g
        (proEtaleConstantRing Y P.Ring) (proEtaleConstantRing Y' P.Ring)
        (proEtaleConstantRing c'.Z P.Ring)
        (proEtaleConstantRingComparison g P.Ring)
        (proEtaleConstantRingComparison c'.g P.Ring)) := by
    rw [proEtaleConstantRingCompositeCoefficients_eq,
      proEtaleConstantRingCompositeCoefficients_eq]
    exact congr_arg_heq (fun h ↦ proEtaleConstantRingComparison h P.Ring)
      properSquare.toCommSq.w
  exact (proEtaleAmbientRingedExchange properSquare
    (proEtaleConstantRing c.Z P.Ring) (proEtaleConstantRing Y P.Ring)
    (proEtaleConstantRing c'.Z P.Ring) (proEtaleConstantRing Y' P.Ring)
    (proEtaleConstantRingComparison c.g P.Ring)
    (proEtaleConstantRingComparison g P.Ring)
    (proEtaleConstantRingComparison gbar P.Ring)
    (proEtaleConstantRingComparison c'.g P.Ring) hcoeff).app
      ((sfIntrinsicDerivedOpen P.Ring c.i).obj M) ≫
    (proEtaleRingDerivedDirectImage c'.g
      (proEtaleConstantRing Y' P.Ring) (proEtaleConstantRing c'.Z P.Ring)
      (proEtaleConstantRingComparison c'.g P.Ring)).map
        ((constantOpenSquareExchange P.coefficients.l P.extension P.level P.level_pos
          g' c'.i c.i gbar openSquare).hom.app M)

/-- The strict finite-level datum transported along the actual geometric-Frobenius
square. M belongs to the recorded bounded constructible finite-Tor category.
The target comparison is precisely the supplied compactification identification;
it is applied before Rf_!(phi_M), keeping the specified Rf_! at both endpoints.
Source: the opening hypotheses and first displayed formula in the blueprint
(blueprint: def-pur-compact-support-transport). -/
def finiteCompactSupportWeilTransport
    (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    (c c' : Compactification (P.frobeniusMap f₀)) (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g (P.frobeniusGaloisMap Y₀))
    (openSquare : IsPullback (P.frobeniusGaloisMap X₀) c'.i c.i gbar)
    (M : finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber X₀).left)
    (φM : (proEtaleConstantRingDerivedPullback P.Ring
      (P.frobeniusGaloisMap X₀)).obj M.obj ≅ M.obj)
    (comparison :
      sfIntrinsicDerivedOpen P.Ring c'.i ⋙
          proEtaleRingDerivedDirectImage c'.g
            (proEtaleConstantRing (P.frobeniusFiber Y₀).left P.Ring)
            (proEtaleConstantRing c'.Z P.Ring)
            (proEtaleConstantRingComparison c'.g P.Ring) ≅
        sfIntrinsicDerivedOpen P.Ring c.i ⋙
          proEtaleRingDerivedDirectImage c.g
            (proEtaleConstantRing (P.frobeniusFiber Y₀).left P.Ring)
            (proEtaleConstantRing c.Z P.Ring)
            (proEtaleConstantRingComparison c.g P.Ring)) :=
  finiteCompactSupportTransportExchange P c c' gbar properSquare openSquare M.obj ≫
    comparison.hom.app ((proEtaleConstantRingDerivedPullback P.Ring
      (P.frobeniusGaloisMap X₀)).obj M.obj) ≫
    (sfIntrinsicDerivedOpen P.Ring c.i ⋙
      proEtaleRingDerivedDirectImage c.g
        (proEtaleConstantRing (P.frobeniusFiber Y₀).left P.Ring)
        (proEtaleConstantRing c.Z P.Ring)
        (proEtaleConstantRingComparison c.g P.Ring)).map φM.hom

section SuppliedStage

variable {DX : Type uX} {DB : Type uB} {DY : Type uY} {DB' : Type uB'}
  [Category.{vX} DX] [Category.{vB} DB] [Category.{vY} DY] [Category.{vB'} DB']

/-- Compact-support transport on the supplied closed coefficient domains:
phi_(f_! M) = Ex_!(M) followed by Rf_!(phi_M).
The repeated X and Y categories encode the first Frobenius square. The comparison
identifies the base-changed chosen compactification with the specified Rf_!.
For integral coefficients the operations are completed; rational and common-stage
operations and comparisons are the supplied transports of def-exchange-projection.
Source: the first displayed composite in the blueprint
(blueprint: def-pur-compact-support-transport). -/
def compactSupportWeilTransport
    (s : SuppliedExchangeProjection.ExchangeProjectionStage
      (DX := DX) (DB := DB) (DY := DY) (DX' := DX) (DB' := DB') (DY' := DY))
    (comparison : s.compactSupport' ≅ s.compactSupport) (M : DX)
    (φM : s.horizontal'.obj M ≅ M) :
    s.horizontal.obj (s.compactSupport.obj M) ⟶ s.compactSupport.obj M :=
  s.compactExchange.app M ≫ comparison.hom.app (s.horizontal'.obj M) ≫
    s.compactSupport.map φM.hom

end SuppliedStage

/-- Integral compact-support transport uses the completed compact-support exchange,
not the ordinary constant-coefficient exchange. The source is intrinsically complete;
the supplied target identification is the chosen compactification comparison on the
closed domain. The strict datum is a specified isomorphism for completed pullback.
Source: integral-stage clause of the blueprint
(blueprint: def-pur-compact-support-transport). -/
def completedCompactSupportWeilTransport
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} {f : X ⟶ Y} {gX : X ⟶ X} {gY : Y ⟶ Y}
    [QuasiCompact f]
    (c c' : Compactification f) (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g gY)
    (openSquare : OpenImmersionSquare gX c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (M : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (φM : (d.completedPull gX).obj M.obj ≅ M.obj)
    (comparison : cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙ d.push c'.g ≅
      cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g) :
    (d.completedPull gY).obj
        ((d.push c.g).obj ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj M.obj)) ⟶
      (d.push c.g).obj ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj M.obj) :=
  completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha M ≫
    comparison.hom.app ((d.completedPull gX).obj M.obj) ≫
    (cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g).map φM.hom

/-- The scheme-Frobenius form at finite coefficients, for every N on T=X or T=Y.
In particular N may be the chosen compact-support image equipped with its transported
morphism. The comparison is the recorded kappa itself, not an arbitrary isomorphism.
Source: final displayed formula in the blueprint
(blueprint: def-pur-compact-support-transport). -/
def finiteSchemeFrobeniusForm (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring)
    (φN : (proEtaleConstantRingDerivedPullback P.Ring
      (P.frobeniusGaloisMap T₀)).obj N ⟶ N) :
    (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap T₀)).obj N ⟶ N :=
  (P.schemeGeometricFrobeniusComparison T₀).hom.app N ≫ φN

/-- Scheme-Frobenius form on any of the supplied higher-coefficient domains.
Here kappa is the supplied completed, rationalized or common-stage realization of the
comparison of def-pur-scheme-geometric-frobenius, and phi may be the transported datum.
Source: final displayed formula, for every object carrying a datum
(blueprint: def-pur-compact-support-transport). -/
def schemeFrobeniusForm {C : Type uC} [Category.{vC} C]
    (schemePull geometricPull : C ⥤ C) (κ : schemePull ≅ geometricPull)
    (N : C) (φN : geometricPull.obj N ⟶ N) : schemePull.obj N ⟶ N :=
  κ.hom.app N ≫ φN

/-- Rationalization, or passage from a common finite coefficient field, of the specified
compact-support transport. The endpoint comparisons are those supplied in
 def-exchange-projection, including its identity and composition normalizations;
there is no rational-to-finite reduction.
Source: field-stage clause of the blueprint
(blueprint: def-pur-compact-support-transport). -/
def compactSupportWeilTransportRepresentative
    {DX : Type uX} {DB : Type uB} {DY : Type uY} {DB' : Type uB'}
    [Category.{vX} DX] [Category.{vB} DB] [Category.{vY} DY] [Category.{vB'} DB']
    (s : SuppliedExchangeProjection.ExchangeProjectionStage
      (DX := DX) (DB := DB) (DY := DY) (DX' := DX) (DB' := DB') (DY' := DY))
    (comparison : s.compactSupport' ≅ s.compactSupport) (M : DX)
    (φM : s.horizontal'.obj M ≅ M)
    {D : Type uD} [Category.{vD} D] (inclusion : DY ⥤ D) {K' L' : D}
    (source : K' ≅ inclusion.obj (s.horizontal.obj (s.compactSupport.obj M)))
    (target : inclusion.obj (s.compactSupport.obj M) ≅ L') : K' ⟶ L' :=
  SuppliedExchangeProjection.exchangeProjectionCoefficientRepresentative
    inclusion source target (compactSupportWeilTransport s comparison M φM)

end WeilConjectures.Purity
