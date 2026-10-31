/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralTower.PurStrictIntegralExchangeData

/-! # PurIntegralStrictCalculus -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Strict proper/open maps have their specified mate normalizations and obey identity,
horizontal pasting and vertical interchange before derived inverse limit.

Source: constituent compatibility, strict integral normalization steps 10--12 and
14 (blueprint: lem-pur-integral-strict-calculus).

Proof: tensor balancing on the ringed diagram site identifies pullComp with the
canonical pullback compositor and pullId with its unit. Taking proper mates gives
the prescribed strict proper exchange. Transpose the strict open comparison: the
normalization equation of cbcStrictExchange and the datum transport identify its
inverse with the pulled open unit and the inverse square compositor. Identity and
successive pullbacks relabel the same test objects and tensors; the unit equations
and mate pasting therefore give the two horizontal identities for their ordered
proper/open composite. In a compatible compactification triangle, the proper/open
mate is determined by the clopen projection which is identity on the open component
and zero on its complement. Those projections commute with relabeling. Proper
mate pasting and open composition give the displayed vertical interchange as an
equality of natural transformations. Restrict scalars to constant coefficients;
unit-normalized scalar comparisons identify composition with the constant-ring
composition of strictTowerProperOpenCalculus and compositionPastingCoherence.
The retained finite-etale-origin witnesses make that comparison invertible at
each level, and exact conservative restriction reflects invertibility of the
strict map. Equality is proved on the diagram site, never reflected from derived
evaluations. Identity factors and zero or empty inputs obey the same formulas. -/
theorem purIntegralStrictCalculus (P : WeilConjectures.PurityFiniteSetting.{t}) :
    PurIntegralStrictMapNormalization (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurIntegralStrictHorizontal (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurIntegralStrictVertical (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) := by sorry

end AlgebraicGeometry.Scheme
