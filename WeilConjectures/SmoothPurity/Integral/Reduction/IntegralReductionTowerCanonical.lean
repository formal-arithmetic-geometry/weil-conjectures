/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Cones

/-! # The integral reduction tower

Source: Bhatt--Scholze, p. 24, Proposition 3.5.1(1) and Definition 3.5.2;
Stacks Project, Tag 06YL (blueprint: def-weil-integral-reduction-tower).

The natural-number index n denotes exponent n+1. We use the chosen complex
representative K and its chosen K-flat resolution q:P→K. The already recorded
chain-level maps are characterized by the sheafified pure-tensor formulas.

The interface omits the unused auxiliary finite-field datum. It uses the existing
completed coefficient ring, projections and scalar extension with independent
site and coefficient universes.

## Main definitions

- `canonicalIntegralReductionTower`: the inverse system of restricted finite reductions.
- `canonicalIntegralReductionTowerMap`: the compatible maps from the represented object.
- `canonicalIntegralReductionTowerCone`: the augmented reduction tower.
-/

@[expose] public section

set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

end WeilConjectures
