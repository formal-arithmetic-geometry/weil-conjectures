/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine
import Sheaf.AlgebraicGeometry.ProjectiveLineConstructible

/-!
# Projective direct-image constructibility

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`thm-fin-projective-constructibility-complete.md`
(blueprint: thm-fin-projective-constructibility-complete).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Every projective morphism between finite-type schemes over `k` satisfies `C(f)`
for the fixed finite coefficient ring and invertible annihilating integer.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`thm-fin-projective-constructibility-complete.md`
(blueprint: thm-fin-projective-constructibility-complete).

Proof plan:
1. Fix the finite coefficient ring `Λ` and integer `N` of `def-finrepair-property-c`.
   For every finite-type `k`-scheme `T`, `thm-fin-projective-line-constructible`
   gives constructibility of every nonnegative higher direct image of every
   constructible `Λ`-module sheaf along the projective-line projection over `T`.
   By `def-finrepair-property-c`, this is `C` for that projection, with precisely
   the same coefficients and annihilating integer. Since `T` is arbitrary, this
   supplies the universal projective-line hypothesis of the reduction lemma.
2. Apply `lem-finrepair-projective-from-line` to obtain `C(f)` for every projective
   morphism between finite-type `k`-schemes. Projectivity is the closed-embedding
   convention of `def-pc-projective-morphism`. This asserts neither arbitrary
   proper direct-image constructibility nor uniform vanishing. -/
theorem hasConstructibleHigherDirectImages_of_isProjective
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsProjective f] :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  sorry

end AlgebraicGeometry.Etale
