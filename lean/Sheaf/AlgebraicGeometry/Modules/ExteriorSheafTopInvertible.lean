/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Invertibility of the top exterior power

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-exterior-sheaf-top-invertible).
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The top exterior power of a constant-rank finite locally free sheaf is invertible.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-exterior-sheaf-top-invertible).

Proof: Choose a cover trivializing `M` with `r` basis sections. On every subopen of
such a chart the basis identifies the module of sections with a free module of rank `r`.
Its top exterior power has the single basis vector given by the wedge of all basis
sections, by `Module.Basis.exteriorPower`. These rank-one identifications commute
with restriction, since the restrictions of the chosen basis sections are the basis
sections on the smaller open. Thus the sectionwise exterior-power presheaf is locally
isomorphic to the structure sheaf; sheafification preserves these identifications.
Each point thus has an open neighbourhood on which the determinant restricts to the
structure sheaf, which is precisely scheme-module invertibility.
For `r = 0` the basis wedge is the empty wedge and the identification is
`exteriorSheaf_zero_iso`. No assumption on nonemptiness of the scheme or on its
characteristic is used. -/
theorem exteriorSheaf_top_isInvertible {X : Scheme.{v}} (M : X.Modules) (r : ℕ)
    [M.IsFiniteLocallyFreeOfRank r] :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (exteriorSheaf M r) := by sorry

end AlgebraicGeometry.Scheme.Modules
