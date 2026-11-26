/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients

/-!
# Completed integral coefficient sheaves

The completed integral coefficient sheaf is the limit of the finite constant ring sheaves
`O_E / ϖ^(n+1)` on the small pro-étale site; this file supplies its commutative ring structure
and limit projections.

## Main definitions

- `integralCoefficientSheafSystem`: the inverse sequence of finite constant ring sheaves.
- `completedIntegralCoefficientSheaf`: its limit in sheaves of rings.
- `completedIntegralCoefficientProjection`: the limit projections.
- `completedIntegralModuleSheaves` and `completedIntegralDerivedCategory`: module categories.
- `completedIntegralCohomology`: cohomology objects of cochain complexes.
- `completedIntegralRestrictScalars`: restriction along each limit projection.

## Implementation details

The natural-number index `n` stands for the positive exponent `n + 1`. Coefficients are
lifted into a universe containing the small pro-étale site. The completion is a limit
of ring sheaves, not the discrete constant sheaf of the valuation ring.

## References

* Bhatt–Scholze, Section 6.5
-/

@[expose] public section

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)






/-- The completed integral coefficient sheaf as a sheaf of commutative rings. Forgetting
commutativity recovers the completed ring sheaf definitionally. -/
noncomputable def completedIntegralCommRingSheaf (D : FiniteFieldDatum.{d})
    (hl : l ≠ D.p) :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
  let _ := hl
  completedIntegralCommRingSheafUnrestricted l E Y

/-- The limit projection as a morphism of commutative ring sheaves. -/
noncomputable def completedIntegralCommRingProjection (n : ℕ) :
    completedIntegralCommRingSheaf l E Y D hl ⟶ integralCoefficientCommRingSheaf l E Y n :=
  completedIntegralCommRingProjectionUnrestricted l E Y n

end WeilConjectures
