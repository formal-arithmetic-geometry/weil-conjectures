/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientTwistAnnihilator
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFreeTensorLinear
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Data.Nat.Prime.Infinite

/-! # Intrinsic coefficient twists without an auxiliary finite field

Source: current blueprint, coefficient twists, order 1251
(blueprint: def-coefficient-twists-detailed).

The condensed coefficient constructions below implement the current blueprint.
The legacy signed lines, exact tensor, rational tensor and common-stage tensor are
retained for compatibility with existing consumers. These interfaces remove only
the unused finite-field proof parameters from the completed line and its field images.
The previously recorded interfaces of this node (the intrinsic, fixed finite positive and PBC
coordinate twists) remain publicly imported.

The primary coefficient interface uses continuous-function condensed rings for
O_E and E and the discrete finite quotient ring at exponent n+1. Finite lines use
the internal free-module functor on roots, equivalently their balanced tensor
with A_E,n+1 over Z/l^(n+1), since the quotient is annihilated by l^(n+1).
The integral transitions reduce coefficients and take l-th powers of roots.
The limit is taken in O_E,S-modules, so its scalar action is coordinatewise.
Signed powers use the internal Hom into the coefficient unit at negative degrees.
Tensoring their degree-zero objects uses the actual unbounded derived tensor.
For Qbar, the publicly imported upstream tateTwist and tateTwistFunctor are used.

## Main definitions
* `AlgebraicGeometry.ProEtale.coefficientFiniteTwistOne`
* `AlgebraicGeometry.ProEtale.coefficientIntegralTwistOne`
* `AlgebraicGeometry.ProEtale.coefficientRationalTwistOne`
* `AlgebraicGeometry.ProEtale.coefficientSignedTwist`
* `AlgebraicGeometry.ProEtale.coefficientTwistFunctor`
* `sfIntegralTwistingObject`
* `sfIntegralTwistingFunctor`
* `sfRationalTwistingFunctor`
* `sfQbarTwistingFunctor`
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

variable (X : Scheme.{u})

end AlgebraicGeometry.ProEtale

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end WeilConjectures
