/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs

/-!
# Exactness of the extension by zero on the pro-étale site

For an open immersion `j : U ⟶ X` the extension by zero `j_!` on sheaves for the small
pro-étale sites is exact (blueprint `lem-weil-extension-by-zero-exact`): it is a left adjoint,
hence right exact, and it is left exact
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`), being the
presheaf-level extension by zero, which is computed objectwise, followed by sheafification.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `lem-weil-extension-by-zero-exact`: Exactness of extension by zero. For an open
immersion `j : U ⟶ X`, the extension by zero `j_!` of pro-étale sheaves with values in a
Grothendieck abelian category `A` (for instance modules over a finite commutative ring such as
`A_{E,n}`) sends short exact sequences to short exact sequences: it preserves finite limits
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`) and, being a left
adjoint, finite colimits. -/
theorem shortExact_map_openImmersionLowerShriek
    {S : ShortComplex (Sheaf (Scheme.ProEt.topology U) A)} (hS : S.ShortExact) :
    (S.map (j)_!open[A]).ShortExact :=
  hS.map_of_exact _

/-- The extension by zero `j_!` along an open immersion is exact: it preserves finite limits and
finite colimits (blueprint `lem-weil-extension-by-zero-exact`). -/
theorem preservesFiniteLimits_and_preservesFiniteColimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open[A] ∧ PreservesFiniteColimits (j)_!open[A] :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale
