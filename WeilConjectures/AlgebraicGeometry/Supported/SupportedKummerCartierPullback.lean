/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.PicardTensorDualComparisonIso

/-!
# Cartier line bundle and canonical section under Cartier-preserving pullback

Source: Stacks Project, Tag 0C4U, lemma-pullback-effective-Cartier-divisors
(blueprint: lem-asd-supported-kummer-cartier-pullback).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible

variable {T T' : Scheme.{u}}

end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
