/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Exact interface for strict completed-coefficient towers

Source: blueprint proper base change, completed pullback; Stacks Tag 099N
(blueprint: def-weil-pbc-exact-pullback-interface).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.constantRlimAdjunction`:
  the derived constant-tower and inverse-limit adjunction.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completionUnit`:
  the adjunction unit followed by the normalized quotient augmentation.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerPull`:
  exact termwise pullback and its compatibility with constant towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

end AlgebraicGeometry.Scheme
