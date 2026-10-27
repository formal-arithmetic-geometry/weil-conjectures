/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Data.Finsupp.Basic

/-! # Effective Q-Cartier Weil divisors on schemes

Source: Stacks Project, Divisors, Tags 0BE2, 02RJ, 01WR; ILO VIII 5.3.8, p.125
(blueprint: def-per-effective-q-cartier-weil-divisor).

On a normal Noetherian scheme, codimension-one points correspond to integral
codimension-one closed subschemes by taking their reduced closures.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- Generic points of prime divisors, with codimension measured by local dimension.
Source: Stacks Tag 0BE2 (blueprint: def-per-effective-q-cartier-weil-divisor). -/
def WeilPrime (X : Scheme.{u}) := {x : X // ringKrullDim (X.presheaf.stalk x) = 1}

/-- Finite integral combinations of integral codimension-one reduced closures.
Source: Stacks Tag 0BE2 (blueprint: def-per-effective-q-cartier-weil-divisor). -/
abbrev WeilDivisor (X : Scheme.{u}) := WeilPrime X →₀ ℤ

/-- The support is the union of the closures of prime divisors with nonzero coefficient.
Source: Stacks Tag 0BE2 (blueprint: def-per-effective-q-cartier-weil-divisor). -/
def WeilDivisor.support {X : Scheme.{u}} (E : X.WeilDivisor) : Set X :=
  ⋃ p ∈ Finsupp.support E, closure ({p.val} : Set X)

/-- The Weil divisor of an effective Cartier ideal is given by the lengths of its
local equations at codimension-one points. On a normal Noetherian scheme those
local rings are DVRs, so these lengths are the normalized orders of vanishing.
The equations are required on an affine neighbourhood of every point.
Source: Stacks Tags 02RJ and 01WR
(blueprint: def-per-effective-q-cartier-weil-divisor). -/
def IdealSheafData.HasEffectiveWeilDivisor {X : Scheme.{u}}
    (C : X.IdealSheafData) (E : X.WeilDivisor) : Prop :=
  C.IsInvertible ∧ ∀ x : X,
    ∃ (U : X.affineOpens) (_hx : x ∈ U.1) (c : Γ(X, U.1)),
      c ∈ nonZeroDivisors Γ(X, U.1) ∧ C.ideal U = Ideal.span {c} ∧
        ∀ (p : X.WeilPrime) (hp : p.val ∈ U.1),
          0 ≤ E p ∧ Ring.ord (X.presheaf.stalk p.val)
            ((X.presheaf.germ U.1 p.val hp).hom c) = ((E p).toNat : ℕ∞)

/-- An effective Weil divisor is Q-Cartier when one positive integer multiple is
an effective Cartier divisor. This quantifies over one integer globally, and keeps
the coefficients through the local order formula, rather than just recording support.
Source: ILO VIII 5.3.8, p.125; Stacks Tags 0BE2, 02RJ and 01WR
(blueprint: def-per-effective-q-cartier-weil-divisor). -/
def WeilDivisor.IsEffectiveQCartier {X : Scheme.{u}} (E : X.WeilDivisor) : Prop :=
  (∀ p, 0 ≤ E p) ∧ ∃ (n : ℕ) (_hn : 0 < n) (C : X.IdealSheafData),
    C.HasEffectiveWeilDivisor (n • E)

end AlgebraicGeometry.Scheme
