/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.Current.IntegralCurrentLimitFactorization

/-! # Native factor of the compact-support/limit comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified quasi-compact-open/total-limit mate is invertible on whole towers.

Source: latest blueprint, integral direct-image proof (2), exact products and open
extension; Stacks Tag 09BP and the augmentation-preserving strict-limit comparison.
(blueprint: lem-sp-current-open-limit-mate).

Proof in words:
1. Present the scheme open immersion by its localized pro-etale slice site. Identify
the integral open functor with the ringed extension by zero through its adjunction,
retaining its unit. Quasi-compactness gives preservation of countable products;
open extension is exact, and countable products of pro-etale modules are exact.
2. Restrict the whole finite-coefficient diagram to integral scalars. On every open
extension summand the restriction/open comparison is the identity, so it commutes
with every quotient transition. The ringed open scalar adjunction theorem identifies
its transpose with the prescribed scalar/pullback square, including the unit.
3. Apply the exact-product-functor strict-limit theorem to this fixed-ring open
functor. Its signed Roos construction gives an invertible comparison and preserves
strict augmentations. The open scalar/limit coherence square identifies this with
the comparison after restricting the whole coefficient diagram.
4. Transport along the pinned coefficient and realization equivalences. Total right
derived uniqueness and the ordinary-unit normalization of A identify the resulting
comparison with the right mate of nativeOpenScalar, hence exactly openLimitMate.
This proves invertibility of the specified map, not just an object isomorphism.
No boundedness is needed in the signed Roos construction; the empty open and zero
tower are included. -/
theorem open_limit_mate_isIso (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (C : spDerivedCoefficientTowers l E U (s.towers U)) :
    IsIso ((openLimitMate l E s q hq A j).app C) := by sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
