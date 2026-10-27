/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.CompletedSupportIntermediateTowerCore

/-! # Reduction of one completed compact-support exchange

Source: Stacks 099M, 099N and 09AE, and the strict proper/open tensor square in
Steps 9--10 of lem-cbc-completed-support-intermediate-tower.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower
open AlgebraicGeometry.ProEtale.StrictTower OrderedExchange

/-- The reduced exchange square before applying derived inverse limit.
Source: Stacks 099M, 099N, 09AE; intermediate-tower proof Steps 9--10.
Proof: first use the proper counit-tensor square on the single strict quotient
coefficient diagram. Transposition under the proper adjunctions identifies its
horizontal arrows with properProjection and its vertical arrows with the proper
square mates. For the open factor transpose the pulled-back open unit: tensor
reassociation carries it to the same open unit tensored with 1, so its inverse
mate is beta. Paste these squares to obtain the ordinary reduction square for
the proper-then-open exchange. The completion units become invertible after
reduction by strictUnits. Naturality of those units moves them past the ordinary
exchange; cancel their reductions on both endpoints. By the definitions of theta,
pullReduction and completedExchange the resulting square is precisely the one
below. All steps are in the derived category of strict diagrams; no equality is
inferred from levelwise evaluations or from applying Rlim.
(blueprint: lem-cbc-completed-support-exchange-reduction). -/
theorem completedExchange_reduction {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X U Y X' U' Y' : Scheme.{t}}
    (j : X ⟶ U) (p : U ⟶ Y) (j' : X' ⟶ U') (p' : U' ⟶ Y')
    (x : X' ⟶ X) (u : U' ⟶ U) (y : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] [QuasiCompact j] [QuasiCompact j']
    [IsProper p] [IsProper p'] (hj : x ≫ j = j' ≫ u) (hp : u ≫ p = p' ≫ y)
    (sj : IsPullback x j' j u) (sp : IsPullback u p' p y) :
    whiskerRight (completedExchange d j p j' p' x u y hj hp sj) (reduction d Y') ≫
        whiskerLeft (completePull d x) (theta d j' p') ≫
          whiskerRight (pullReduction d x) (tower (A := A) j' p') =
      whiskerLeft (completed d j p) (pullReduction d y) ≫
        whiskerRight (theta d j p) (G A y) ≫
          whiskerLeft (reduction d X) (strictExchange j p j' p' x u y hj hp sj) := by
  sorry

end AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower
