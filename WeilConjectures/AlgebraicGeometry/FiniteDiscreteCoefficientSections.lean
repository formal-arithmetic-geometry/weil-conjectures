/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal

/-! # The coefficient maps on sections under direct image -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

attribute [local irreducible] upperStar upperStarLowerStarAdjunction

end AlgebraicGeometry.ProEtale.CondensedRing
