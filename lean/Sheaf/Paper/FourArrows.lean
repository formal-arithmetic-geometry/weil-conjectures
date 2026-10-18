/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
public import Sheaf.Paper.FiniteLevelProEtaleBaseChange
public import Sheaf.Paper.CompletedPullback

/-!
# The four finite-level arrows

Source: blueprint, proper base change, four finite-level arrows, order 1343;
Stacks Project Tags 07A7, 09C9, 0B56 and 0944 (blueprint: def-weil-pbc-four-arrows).

The horizontal arrows and the finite exchange are isomorphisms. The reduced ambient
exchange is a morphism; neither its invertibility nor commutativity of this square is
part of this definition. All scalar extensions and pullbacks are uncompleted.

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourArrows`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The finite-coefficient projection is the adjunct of chi followed by scalar extension
of the ambient counit. Its target retains the quotient-coefficient action.
Source: blueprint four arrows; Stacks Tags 0B56 and 0944
(blueprint: def-weil-pbc-four-arrows). -/
noncomputable def AdicCoefficientDatum.finiteProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : d.derived X) (n : ℕ) :
    (d.reduction Y n).obj ((d.push f).obj H) ⟶
      (d.finitePush f n).obj ((d.reduction X n).obj H) :=
  (proEtaleRingDerivedAdjunction f (d.finiteRing Y n) (d.finiteRing X n)
    (d.finiteRingIso f n)).homEquiv _ _
      ((d.chi f n).hom.app ((d.push f).obj H) ≫
        (d.reduction X n).map
          ((proEtaleRingDerivedAdjunction f (d.completedRing Y) (d.completedRing X)
            (d.integralRingIso f)).counit.app H))

/-- The specified finite projection is invertible, also without properness or a bound on H.
Source: blueprint four arrows; Stacks Tags 0944, 0D6D and 0D6E
(blueprint: def-weil-pbc-four-arrows).
Proof: the coefficient-change adjunction comparison identifies the restriction of this
adjunct with the canonical uncompleted projection-formula mate for (P_n)_Y. The perfect
coefficient theorem lemma-weil-pbc-perfect-projection-formula gives the signed finite-total
inverse. Exact restriction reflects derived isomorphisms by
lem-weil-pbc-ring-sheaf-change-adjunction, hence the original quotient-linear map is an
isomorphism. The same argument applies to f' and H = Lg'*K. -/
theorem AdicCoefficientDatum.finiteProjection_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : d.derived X) (n : ℕ) : IsIso (d.finiteProjection f H n) := by
  sorry

attribute [instance] AdicCoefficientDatum.finiteProjection_isIso

/-- A square of four arrows with exactly the asserted three isomorphisms. No equation
between its two paths is imposed. Source: blueprint four arrows
(blueprint: def-weil-pbc-four-arrows). -/
structure FourFiniteLevelArrows {C : Type v} [Category.{w} C] (corners : Fin 4 → C) where
  h : corners 0 ≅ corners 1
  h' : corners 2 ≅ corners 3
  v : corners 0 ⟶ corners 2
  v' : corners 1 ≅ corners 3

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The finite proper-base-change theorem in the normalized corner notation.
Source: blueprint four arrows, Stacks 09C9
(blueprint: def-weil-pbc-four-arrows).
Proof: apply finiteLevelProEtaleBaseChange to the finite quotient and its retained
etale witness. The finiteExchange abbreviation is exactly that canonical ringed
adjunction mate, so the conclusion is unchanged. -/
theorem AdicCoefficientDatum.finiteExchange_isIso [IsProper f]
    (K : d.derived X) (n : ℕ)
    (W : FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    IsIso ((d.finiteExchange sq n).app ((d.reduction X n).obj K)) := by
  sorry

/-- The finite exchange is the canonical ambient exchange with its isomorphism certified
by finite-level proper base change and the specified witness. The underlying morphism
contains no witness choices. Source: blueprint four arrows; Stacks Tags 07A7 and 09C9
(blueprint: def-weil-pbc-four-arrows). -/
noncomputable def AdicCoefficientDatum.finiteExchangeIso [IsProper f]
    (K : d.derived X) (n : ℕ)
    (W : FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    (d.finitePull g n).obj ((d.finitePush f n).obj ((d.reduction X n).obj K)) ≅
      (d.finitePush f' n).obj ((d.finitePull g' n).obj ((d.reduction X n).obj K)) :=
  @asIso _ _ _ _ ((d.finiteExchange sq n).app ((d.reduction X n).obj K))
    (d.finiteExchange_isIso sq K n W)

/-- The four specified arrows at positive level n+1: pullback of the finite projection;
projection followed by pushforward of delta; chi followed by reduction of the ambient
exchange; and the canonical finite-coefficient exchange. The family W retains separate
bounded-below etale witnesses, with no uniform bound or compatibility requirement.
Source: blueprint four arrows, order 1343; Stacks Tags 07A7, 09C9, 0B56 and 0944
(blueprint: def-weil-pbc-four-arrows). -/
noncomputable def AdicCoefficientDatum.fourArrows [IsProper f] (K : d.derived X)
    (_hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) :
    FourFiniteLevelArrows (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n) where
  h := asIso ((d.finitePull g n).map (d.finiteProjection f K n))
  h' := asIso (d.finiteProjection f' ((d.pull g').obj K) n ≫
    (d.finitePush f' n).map ((d.delta (g' := g') K n).hom))
  v := (d.chi g n).hom.app ((d.push f).obj K) ≫
    (d.reduction Y' n).map ((d.integralExchange sq).app K)
  v' := d.finiteExchangeIso sq K n (W n)

end AlgebraicGeometry.Scheme
