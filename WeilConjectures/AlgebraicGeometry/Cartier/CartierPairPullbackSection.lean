/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerCartierPullback
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierPairTensorAddition
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison
import all WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange

/-! # Pullback of the Cartier line bundle with its canonical section

Source: Stacks Project, Tag 0C4U, and the relative Cartier class in the blueprint
proof of lem-amb-cartier-kummer-map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
