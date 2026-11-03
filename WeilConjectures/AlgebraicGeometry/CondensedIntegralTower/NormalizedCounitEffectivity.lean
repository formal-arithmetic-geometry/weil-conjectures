/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedAdjunctionCoordinates

/-! # Effectivity for the actual counit of reduction and inverse limit
Source: sk-lem-sp-tower-equivalence, Counit paragraph.
(blueprint: lem-sp-normalized-counit-effectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The finite components of the actual counit are invertible on every normalized
unbounded tower. No cohomological, Tor or constructibility bound is imposed.
Source: sk-lem-sp-tower-equivalence.proof.md, Counit paragraph
(blueprint: lem-sp-normalized-counit-effectivity).

Proof: the projection normalization identifies the scalar transpose of each
limit projection with this evaluated counit, using the canonical level comparison.
Compute the right-derived limit on a K-injective strict-system representative and
compare it with the restricted-level Roos fiber using exact countable products.
Resolve each quotient by its two-term free scalar resolution. After normalization,
the quotient-error fiber at level m is the system C_m[1] with power-of-ell
transitions. A sufficiently long composite of these transitions is zero since
ell^(m+1) annihilates C_m. The finite geometric sum therefore inverts one minus
the Roos shift, so this error fiber has zero limit. Tensor by the bounded free
resolution commutes with the countable product and fiber. Hence the scalar
transpose of each actual projection is an isomorphism, as asserted by
lem-coef-normalized-dvr-effectivity. The projection identities ensure that the
result concerns the displayed counit rather than an independently chosen map. -/
theorem normalized_counit_effectivity (D : Model l E T) (adj : D.red ⊣ D.rlim)
    (hp : LimitProjectionsNormalized l E T D adj)
    (C : DerivedTowers l E T)
    (hC : ∀ (m n : ℕ) (h : m ≤ n), IsIso ((D.reduction h).app C)) :
    ∀ m : ℕ, IsIso ((D.levels m).inv.app (D.rlim.obj C) ≫
      (evaluation l E T m).map (adj.counit.app C)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
