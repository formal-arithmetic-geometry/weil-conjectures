/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.Paper.QbarProperBaseChange
public import Sheaf.Paper.GeometricFiberFiniteExtension
public import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.Paper.PbcScalarExtension

/-! # Geometric-fiber proper base change with Qbar_l coefficients

Source: Weil-conjectures blueprint main-20261015, `sec-proper-base-change`,
`sk-thm-properbasechange`, corollary `cor-weil-pbc-geometric-fiber-qbar`
(blueprint: cor-weil-pbc-geometric-fiber-qbar).

The coefficient category and exchange presentation are the existing finite-stage pair
category and the canonically normalized operations. The geometric fiber is the scheme
pullback, with its identity chosen pullback identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The descended geometric-fiber exchange is invertible, and at a finite overfield it
is represented by the rational finite-extension geometric-fiber exchange on the scalar
extension of the given representative. The existential presentation supplies the actual
operations of prop-weil-pbc-descent-functors with their canonical scalar comparisons and
localized completed exchange; it is not an assumption of constructible preservation.
Its `exchange_eq` identifies the finite-stage arrow with the exchange used by
cor-weil-pbc-geometric-fiber-finite-extension, in the small coefficient-field presentation.
The equality with `atStage` includes precisely the endpoint scalar comparisons.
Source: blueprint main-20261015, `sec-proper-base-change`, `sk-thm-properbasechange`,
corollary `cor-weil-pbc-geometric-fiber-qbar`
(blueprint: cor-weil-pbc-geometric-fiber-qbar).

Proof:
1. Specialize thm-weil-pbc-qbar to `geometricFiberSquare f ybar`: its bottom arrow is
   `ybar`, its upper arrow is `pullback.fst f ybar`, its left arrow is
   `pullback.snd f ybar`, and the chosen pullback identification is the identity.
   All scheme hypotheses are those imposed here, and the theorem allows arbitrary
   bottom arrows. Its descended exchange is therefore the required isomorphism.
2. For the pair representative `K = (E, K_E)`, the representative clause of that
   theorem gives a finite overfield `M` containing `E`. The transition functor of
   prop-weil-pbc-scalar-extension sends `K_E` to `T_{M/E} K_E` in the raw rational
   category. Apply cor-weil-pbc-geometric-fiber-finite-extension at `M` to this object:
   its hypotheses concern the same schemes and are independent of the finite field.
   The square and the specified localized completed exchange are identical, so its
   exchange is the stage component in `atStage`, conjugated by the canonical scalar
   comparisons. This proves both finite-stage invertibility and the representative
   equality. No condensed-coefficient identification or Karoubi envelope is used. -/
theorem geometricFiber_qbar_properBaseChange
    (l : ℕ) [Fact l.Prime]
    (Qbar : Type w) [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ybar : Spec (.of Ω) ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsNoetherian (pullback f ybar)] [IsNoetherian (Spec (.of Ω))]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [Fact (∃ n : ℕ,
      topologicalKrullDim (pullback f ybar : Scheme.{u}) ≤ (n : WithBot ℕ∞))]
    [Fact (∃ n : ℕ,
      topologicalKrullDim (Spec (.of Ω) : Scheme.{u}) ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    [Fact (∀ x : (pullback f ybar : Scheme.{u}),
      IsUnit (l : (pullback f ybar).presheaf.stalk x))]
    [Fact (∀ y : Spec (.of Ω), IsUnit (l : (Spec (.of Ω)).presheaf.stalk y))]
    [IsProper f] [IsProper (pullback.snd f ybar)]
    (e : ℕ)
    (_hFibres : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
      (y : Spec (.of Ω') ⟶ Y),
      (pullback f y : Scheme.{u}).dim ≤ (e : WithBot ℕ∞)) :
    ∃ P : PbcQbarExchangePresentation l Qbar (geometricFiberSquare f ybar),
      ∀ K : pbcQbarCategory l Qbar X,
        IsIso (P.exchange.app K) ∧
        ∃ (M : Padic.FiniteCoefficientFields l Qbar) (h : K.stage ≤ M),
          IsIso ((P.Ex.τ M).app
            ((pbcScalarSystem l Qbar X dX.out iX.out).T h |>.obj K.obj)) ∧
          P.exchange.app K =
            PbcQbarExchangePresentation.atStage l Qbar (geometricFiberSquare f ybar)
              P K M h := by
  sorry

end AlgebraicGeometry.Scheme
