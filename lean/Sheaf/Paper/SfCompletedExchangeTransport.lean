/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z9
-/
module

public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.Paper.ExchangeFunctoriality

/-! # Canonical comparison of the two completed exchange presentations

Source: Stacks Tags 099N and 07A7; the ordinary-to-completed normalization in
blueprint six-functor package clause (4).
(blueprint: lem-sf-completed-exchange-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The smooth-base-change completed mate agrees with the ordered proper-base-change
construction under the fixed coefficient and resolving-counit comparisons. No
properness, smoothness, constructibility or dimension hypothesis is needed.
Source: Stacks Tags 099N and 07A7; blueprint package clause (4), completed
normalization step (blueprint: lem-sf-completed-exchange-transport).

Proof: the coefficient structure maps agree after every quotient projection, so the
completed coefficient maps agree. Transport ordinary pullback by the two canonical
resolving counits; their uniqueness identifies the units, counits and tensor-balanced
composition comparisons. Taking the ordinary mate therefore identifies the ordinary
exchange, including the direct-image comparisons at both ends. Precompose the desired
equality by the ordinary-to-completed unit at the direct image of K. The normalized
completed adjunction gives ordinary exchange followed by the target completion unit
on the left. On the right, the unit equation for cbcDatumCompletedTransport and
completedExchange_unit give the identical arrow, using naturality of the direct-image
comparison. The target is intrinsically complete because completed pullback and
direct image preserve intrinsic completeness. The injective part of the completion
reflector bijection cancels the source unit. This proves equality of the specified
maps, without deducing it merely from their separate finite evaluations. The same
argument includes zero inputs and empty schemes. -/
theorem sfCompletedExchange_transport (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : ChosenCartesianSquare g' f' f g) (K : PbcComplete l E X) :
    let pushComparison := fun {V W : Scheme.{u}} (q : V ⟶ W) ↦
      eqToIso (congrArg (proEtaleRingDerivedDirectImage q
        (pbcAdicCompletion W (pbcIntegralDatum l E))
        (pbcAdicCompletion V (pbcIntegralDatum l E)))
        (Iso.ext (cbcDatumCoefficient_eq (pbcIntegralDatum l E) q)))
    ((sbcExchangeApp l E (exchangeTransposeSquare sq) K).hom =
        (cbcDatumCompletedTransport (pbcIntegralDatum l E) g).hom.app
            ((sbcPush l E f).obj K).obj ≫
          ((pbcIntegralDatum l E).completedPull g).map
            ((pushComparison f).hom.app K.obj) ≫
          (pbcIntegralDatum l E).completedExchange sq K.obj ≫
          ((pbcIntegralDatum l E).push f').map
            ((cbcDatumCompletedTransport (pbcIntegralDatum l E) g').inv.app K.obj) ≫
          (pushComparison f').inv.app ((sbcPull l E g').obj K).obj) := by
  sorry

end WeilConjectures
