/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-! The complementary component of the varying-ring clopen projection is zero.
Source: the complementary-component calculation in the proof of

`lem-sp-varying-ring-proper-open-pasting`
(blueprint: new-lem-sp-varying-ring-module-pi-complement-zero).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- Restriction of the clopen projection to the complementary open vanishes.
Source: Stacks 09AE and the complementary-component part of the clopen projection
calculation in `lem-sp-varying-ring-proper-open-pasting`.
Proof: pull a module back to the complementary open.  The image of the clopen
projection is supported on the disjoint image open, so its restriction is zero.
The assertion is checked on pro-etale test objects, where the two disjoint opens
have empty pullback; the sheaf terminal-section property then identifies every
section with zero.  The same calculation is compatible with all semilinear
transitions.
(blueprint: new-lem-sp-varying-ring-module-pi-complement-zero). -/
theorem modulePi_complement_zero {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Modules R φ X) :
    (pull R φ c).map ((modulePi R φ s).app M) = 0 := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
