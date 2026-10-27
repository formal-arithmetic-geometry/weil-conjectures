/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.Paper.SixFunctorOperationDatumStages

/-! # Compact-support exchange in operation coordinates

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, clause (iii): the specified compact-support
exchange in the base-change square
(blueprint: def-sf-compact-exchange-operation-coordinates).

This definition transports the stage's specified map through its recorded functor
equalities. It assumes no exchange theorem and asserts no invertibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory
namespace WeilConjectures

/-- The specified compact-support exchange, with the source and target functors
written using the supplied operation stage. The two equality isomorphisms only
change coordinates on the already defined compact exchange.
Source: def-sf-operation-stages and def-exchange-projection; current blueprint,
lem-sf-kunneth-coherence.proof.md, clause (iii)
(blueprint: def-sf-compact-exchange-operation-coordinates). -/
def sixFunctorCompactExchange {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q) :
    S.support Q.f Q.compactification ⋙ S.pull Q.g ⟶
      S.pull Q.g' ⋙ S.support Q.f' Q.compactification' :=
  (eqToIso (congrArg₂ (fun F G ↦ F ⋙ G) A.compactSupport A.horizontal)).inv ≫
    A.stage.compactExchange ≫
    (eqToIso (congrArg₂ (fun F G ↦ F ⋙ G) A.horizontal' A.compactSupport')).hom

end WeilConjectures
