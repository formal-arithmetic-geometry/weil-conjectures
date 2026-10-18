/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Exactness of extension by zero in intrinsic coefficients

Source: Weil blueprint, order 1492; Stacks Project, Tags 03DI and 03DJ
(blueprint: lem-weil-extension-by-zero-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Extension by zero is additive and preserves finite limits and colimits.
Source: blueprint order 1492; Stacks, Tags 03DI and 03DJ
(blueprint: lem-weil-extension-by-zero-exact).

Proof: identify the open small site with the localization of the ambient small site
(lem-weil-proetale-weakly-etale-localization). The presheaf extension has one summand
when a factorization exists and zero otherwise, since the open immersion is monic.
The exact localization extension-by-zero theorem
(lem-pur-site-restriction-module-adjunction-exact) therefore applies to the very
presheaf and module sheafification in def-weil-extension-by-zero. The canonical
realization equivalences preserve addition, limits and colimits, so transport preserves
these three assertions. -/
theorem sfIntrinsicExtensionByZero_exact {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicExtensionByZero j A).Additive ∧
      PreservesFiniteLimits (sfIntrinsicExtensionByZero j A) ∧
      PreservesFiniteColimits (sfIntrinsicExtensionByZero j A) := by
  sorry

/-- Additivity from the exactness assertion. Source: Stacks, Tag 03DJ
(blueprint: lem-weil-extension-by-zero-exact). -/
noncomputable instance sfIntrinsicExtensionByZero_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicExtensionByZero j A).Additive :=
  (sfIntrinsicExtensionByZero_exact j A).1

/-- Left exactness from the exactness assertion. Source: Stacks, Tag 03DJ
(blueprint: lem-weil-extension-by-zero-exact). -/
noncomputable instance sfIntrinsicExtensionByZero_preservesFiniteLimits
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A] :
    PreservesFiniteLimits (sfIntrinsicExtensionByZero j A) :=
  (sfIntrinsicExtensionByZero_exact j A).2.1

/-- Right exactness from the exactness assertion. Source: Stacks, Tag 03DJ
(blueprint: lem-weil-extension-by-zero-exact). -/
noncomputable instance sfIntrinsicExtensionByZero_preservesFiniteColimits
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A] :
    PreservesFiniteColimits (sfIntrinsicExtensionByZero j A) :=
  (sfIntrinsicExtensionByZero_exact j A).2.2

end AlgebraicGeometry.Scheme
