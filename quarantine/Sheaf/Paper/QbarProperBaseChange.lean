/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Paper.PbcDescentFunctors
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.Paper.FiniteExtensionProperBaseChange
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.IntrinsicQbarCategory

/-! # Proper base change with Qbar_l coefficients

Source: Weil blueprint main-20261015, proper base change, order 1419
(blueprint: thm-weil-pbc-qbar).

The presentation below records the canonical operations and exchange of the descent
proposition. It introduces no new coefficient category or exchange construction.
The theorem supplies this presentation, rather than assuming preservation or an
unspecified family of functors. Its exchange is defined by the actual descent formula.

## Main definitions

* `PbcQbarExchangePresentation`: the canonically specified descent witnesses.
* `PbcQbarExchangePresentation.exchange`: their descended exchange.
* `PbcQbarExchangePresentation.atStage`: its finite-overfield representative.

## Main statements

* `qbar_properBaseChange`: invertibility, the stage formula and representative independence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y X' Y' : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : ChosenCartesianSquare g' f' f g)

/-- The witnesses of prop-weil-pbc-descent-functors, with the actual finite-stage
operations, all four canonical beta specifications and the actual localized completed
exchange. These are presentation data for that existing construction, not additional
hypotheses of proper base change. No object is chosen from an existence assertion.
Source: blueprint main-20261015, order 1419, descended exchange
(blueprint: thm-weil-pbc-qbar). -/
structure PbcQbarExchangePresentation where
  presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
      ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj)
  presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X' E),
    PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
      ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj)
  presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω Y E),
    PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
      ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj)
  presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
      ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj)
  Rf : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out)
    (pbcScalarSystem l Ω Y dY.out iY.out)
  Rf' : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X' dX'.out iX'.out)
    (pbcScalarSystem l Ω Y' dY'.out iY'.out)
  Lg : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω Y dY.out iY.out)
    (pbcScalarSystem l Ω Y' dY'.out iY'.out)
  Lg' : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out)
    (pbcScalarSystem l Ω X' dX'.out iX'.out)
  Rf_eq : ∀ E : Padic.FiniteCoefficientFields l Ω,
    Rf.base.Φ E = pbcDescentDirectImage l Ω f presRf E
  Rf_beta : PbcDirectImageBetaSpec l Ω f presRf Rf.base
  Rf'_eq : ∀ E : Padic.FiniteCoefficientFields l Ω,
    Rf'.base.Φ E = pbcDescentDirectImage l Ω f' presRf' E
  Rf'_beta : PbcDirectImageBetaSpec l Ω f' presRf' Rf'.base
  Lg_eq : ∀ E : Padic.FiniteCoefficientFields l Ω,
    Lg.base.Φ E = pbcDescentPullback l Ω g presLg E
  Lg_beta : PbcPullbackBetaSpec l Ω g presLg Lg.base
  Lg'_eq : ∀ E : Padic.FiniteCoefficientFields l Ω,
    Lg'.base.Φ E = pbcDescentPullback l Ω g' presLg' E
  Lg'_beta : PbcPullbackBetaSpec l Ω g' presLg' Lg'.base
  Ex : StageSystem.Morphism.Hom (Rf.base.comp Lg.base) (Lg'.base.comp Rf'.base)
  exchange_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X E),
    HEq ((Ex.τ E).app (ScalarLocalization.mk K))
      ((pbcStageLocalization l Ω Y' E).map
        (ObjectProperty.homMk
          (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
              ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
          (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
              ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
          ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app K.obj)))

namespace PbcQbarExchangePresentation

variable (P : PbcQbarExchangePresentation l Ω sq)

/-- The exchange descended by prop-weil-pbc-descent-functors, with its specified
composition comparisons. Source: blueprint main-20261015, order 1419
(blueprint: thm-weil-pbc-qbar). -/
def exchange : P.Rf.base.functor ⋙ P.Lg.base.functor ⟶
    P.Lg'.base.functor ⋙ P.Rf'.base.functor :=
  (StageSystem.Morphism.functorCompIso P.Rf.base P.Lg.base).inv ≫
    StageSystem.Morphism.descNatTrans P.Ex ≫
      (StageSystem.Morphism.functorCompIso P.Lg'.base P.Rf'.base).hom

/-- The finite-overfield exchange representative, conjugated by precisely the scalar
comparisons of the descended composite families. In particular M may equal K.stage.
Source: blueprint main-20261015, order 1419, finite-stage representation
(blueprint: thm-weil-pbc-qbar). -/
def atStage (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
    (h : K.stage ≤ M) :
    (P.Rf.base.functor ⋙ P.Lg.base.functor).obj K ⟶
      (P.Lg'.base.functor ⋙ P.Rf'.base.functor).obj K :=
  StageSystem.PairCategory.mkHom M h h
    (((P.Rf.base.comp P.Lg.base).β h).hom.app K.obj ≫
      (P.Ex.τ M).app ((pbcScalarSystem l Ω X dX.out iX.out).T h |>.obj K.obj) ≫
        ((P.Lg'.base.comp P.Rf'.base).β h).inv.app K.obj)

end PbcQbarExchangePresentation

/-- Proper base change in the actual Qbar_l coefficient pair categories.
The only geometric extra condition is properness of f; g is arbitrary. The scheme
hypotheses are exactly those required to form the four recorded coefficient categories.
The existential presentation supplies the actual operations and their canonical
normalizations, without asking for preservation as a hypothesis. Every finite-overfield
exchange component is invertible; its class is the descended component. The formula for
every M gives independence of overfield. The final equation identifies the arrows for any
two isomorphic pair representatives, using their actual induced source and target maps.
Since these functors act on quotient Homs, the equation is independent of the morphism
representative of h as well.
Source: blueprint main-20261015, proper base change, order 1419
(blueprint: thm-weil-pbc-qbar).

Proof:
1. Apply thm-weil-pbc-finite-extension to every finite coefficient stage, using the
canonical small field presentation and its coefficient identifications. Properness is
stable under the chosen Cartesian base change. The noetherian finite-dimensional
hypotheses give a uniform bound on geometric fibers of f. The integral preservation
witnesses restrict the four actual operations, and rational transport gives their finite
stage functors. prop-weil-pbc-scalar-extension supplies canonical scalar comparisons,
including identity extensions, and identifies scalar extension of exchange with exchange.
2. prop-weil-pbc-descent-functors assembles exactly these witnesses into the presentation
and descends the compatible exchange family. At (E,K_E), its component is the image of
the E-exchange under the stage inclusion. The inverse finite-stage exchange gives an
inverse in the pair category: identities and compositions are computed at that stage by
def-weil-pbc-finite-stage-pair-category. Hence every descended component is invertible.
3. Scalar compatibility conjugates the M-exchange at T_{M/E} K_E to the transported
E-exchange, giving atStage for every overfield M. The common-stage equality criterion of
prop-weil-pbc-common-stage-calculus identifies two such classes at a common further
field. Naturality of the descended transformation gives the last equation for every
isomorphism h between two pair representatives. Functors preserve the inverse of h, so
this is equality after identifying both endpoints. Quotient Homs already remove every
choice of morphism representative. This is precisely the current blueprint proof's
finite-stage descent, isomorphism and representative-independence argument. -/
theorem qbar_properBaseChange [IsProper f] :
    ∃ P : PbcQbarExchangePresentation l Ω sq,
      (∀ K : pbcQbarCategory l Ω X, IsIso ((P.exchange).app K)) ∧
      (∀ (M : Padic.FiniteCoefficientFields l Ω) (K : pbcStageCategory l Ω X M),
        IsIso ((P.Ex.τ M).app K)) ∧
      (∀ (K : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
        (h : K.stage ≤ M),
        (P.exchange).app K = PbcQbarExchangePresentation.atStage l Ω sq P K M h) ∧
      (∀ (K L : pbcQbarCategory l Ω X) (h : K ≅ L),
        (P.Rf.base.functor ⋙ P.Lg.base.functor).map h.hom ≫ (P.exchange).app L =
          (P.exchange).app K ≫
            (P.Lg'.base.functor ⋙ P.Rf'.base.functor).map h.hom) := by
  sorry

end AlgebraicGeometry.Scheme
