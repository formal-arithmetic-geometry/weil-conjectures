/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Exactness of extension by zero in intrinsic coefficients

Source: Weil blueprint, order 1492; Stacks Project, Tags 03DI and 03DJ
(blueprint: proposition-extension-zero-restriction-closed-subscheme--7).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Extension by zero is additive and preserves finite limits and colimits.
Source: blueprint order 1492; Stacks, Tags 03DI and 03DJ
(blueprint: proposition-extension-zero-restriction-closed-subscheme--7).

Proof: unfold the intrinsic extension as the composite of the inverse canonical
coefficient realization, fixed-coefficient extension by zero, and the ambient canonical
coefficient realization. The realization functors are additive equivalences
(`finiteCoefficientIntrinsicRealization_exact`); their inverses are therefore additive,
and both directions preserve limits and colimits. The middle functor is additive and
preserves finite limits by `openImmersionLowerShriek_additive` and
`preservesFiniteLimits_openImmersionLowerShriek`; it preserves colimits because it is
a left adjoint. Composition gives the three assertions. -/
theorem sfIntrinsicExtensionByZero_exact {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicExtensionByZero j A).Additive ∧
      PreservesFiniteLimits (sfIntrinsicExtensionByZero j A) ∧
      PreservesFiniteColimits (sfIntrinsicExtensionByZero j A) := by
  have hU : (sfIntrinsicModuleEquivalence U A).functor.Additive :=
    ProEtale.finiteCoefficientIntrinsicRealization_additive U A
  have hX : (sfIntrinsicModuleEquivalence X A).functor.Additive :=
    ProEtale.finiteCoefficientIntrinsicRealization_additive X A
  unfold sfIntrinsicExtensionByZero
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity from the exactness assertion. Source: Stacks, Tag 03DJ
(blueprint: proposition-extension-zero-restriction-closed-subscheme--7). -/
noncomputable instance sfIntrinsicExtensionByZero_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicExtensionByZero j A).Additive :=
  (sfIntrinsicExtensionByZero_exact j A).1

/-- Left exactness from the exactness assertion. Source: Stacks, Tag 03DJ
(blueprint: proposition-extension-zero-restriction-closed-subscheme--7). -/
noncomputable instance sfIntrinsicExtensionByZero_preservesFiniteLimits
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A] :
    PreservesFiniteLimits (sfIntrinsicExtensionByZero j A) :=
  (sfIntrinsicExtensionByZero_exact j A).2.1

/-- Right exactness from the exactness assertion. Source: Stacks, Tag 03DJ
(blueprint: proposition-extension-zero-restriction-closed-subscheme--7). -/
noncomputable instance sfIntrinsicExtensionByZero_preservesFiniteColimits
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A] :
    PreservesFiniteColimits (sfIntrinsicExtensionByZero j A) :=
  (sfIntrinsicExtensionByZero_exact j A).2.2

end AlgebraicGeometry.Scheme
