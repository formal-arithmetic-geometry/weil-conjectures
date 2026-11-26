/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import WeilConjectures.SmoothPurity.Supporting.ReducedIntegralBraidingScalarExtensionSquare

/-!
# Integral Koszul braiding and scalar extension

## References

* Stacks Project, Cohomology on Sites, Tag 0FPQ
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/--
The coherently normalized integral Koszul braiding commutes with the prescribed
integral tensor comparison for a finite coefficient extension. -/
theorem integralBraidingScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
        ((pullbackTensorIntegralBraiding l E W M N).hom) ≫
      (integralTensorScalarComparison l E L ι W N M).hom =
    (integralTensorScalarComparison l E L ι W M N).hom ≫
      (pullbackTensorIntegralBraiding l L W
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj N)).hom := by
  apply (integralSystemReduction_fullyFaithful l L W).2.map_injective
  exact reducedIntegralBraidingScalarExtensionSquare l E L ι W M N

end WeilConjectures
