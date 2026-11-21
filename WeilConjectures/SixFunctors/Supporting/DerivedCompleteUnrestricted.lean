/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-!
# Unrestricted derived completeness

A complex is unrestrictedly derived complete if it is derived complete for some choice of
finite-field datum.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Definition 3.5.2, p. 24
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t})

/-- Derived completeness of the completed coefficient sheaf, with no finite-field condition:
it holds for some finite-field datum of characteristic different from `l`, which always
exists. -/
noncomputable def IsDerivedCompleteUnrestricted
    (K : DerivedCategory (integralTowerModules.{t, u} l E Y)) : Prop :=
  ∃ (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p), IsDerivedComplete l E Y D hl K

end WeilConjectures
