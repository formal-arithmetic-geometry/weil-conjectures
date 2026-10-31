/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerPullbackNormalizations

/-! # Normalized IntegralTowerOrdinaryPullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary scalar/pullback isomorphism, normalized on tensor generators.
Source: blueprint direct-image proof paragraphs (2)--(3).
Proof: compare the recorded integral scalar projection with the projection of the
completed coefficient sheaf by completed finite-quotient hom extensionality.
The section/internal equivalence identifies the geometric coefficient map with
the unique map compatible with all completed projections. Apply the normalized
whole strict pullback-tower comparison to complexes concentrated in degree zero,
restricting the uniformizer exponents to ramification times (n+1). Transport
coefficients and transitions by the quotient-system ring-isomorphism comparison,
and transport the integral module coordinate by the internal/section equivalence.
The tensor formula is linear over the finite quotient and so defines maps before
scalar restriction. The normalized scalar adjunction and geometric units identify
its value on one tensor unit_f(x) with unit_f(one tensor x). The specified ordinary
unit-transition compatibility makes these level maps commute with every transition.
Thus they assemble to a strict ordinary tower isomorphism. The fixed evaluations
are identity on sections, so the resulting formula is OrdinaryPullNormalized.
No invertibility of ell or flatness of its quotient is used. The same construction
applies to zero modules, the empty scheme, and level zero.
(blueprint: lem-sp-integral-tower-ordinary-pullback). -/
theorem ordinary_reduction_pullback_exists (s : Presentation l E)
    (e : Evaluation l E s) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ q : OrdinaryPullComparison l E s f, OrdinaryPullNormalized l E s e f q := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
