/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism.Point
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionPoint
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct
public import WeilConjectures.Mathlib.CategoryTheory.Monad.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsCounit

/-!
# All rational points have the same class

Let `a : X ⟶ Spec k` be smooth and proper of pure relative dimension `d` over an algebraically
closed field `k`, with `X` connected, and let `Λ` be a self-injective finite coefficient ring.
For a `k`-point `x` of `X`, write `⌊x⌋ ∈ H^{2d}(X, Λ(d))` for the fundamental class
`[x ⊂ X] ∈ H^{2d}_x(X, Λ(d))` with its supports forgotten. Then `⌊x⌋ = ⌊y⌋` for any two
`k`-points (`AlgebraicGeometry.Etale.fundamentalClass_comp_counit_eq_of_section`).

The point `y` is the base change of the diagonal `Δ : X ⟶ X ×_k X` along the section
`j_y = (𝟙, a ≫ y)` of the first projection, so `⌊y⌋` is the restriction of `⌊Δ⌋` along `j_y`
(`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_isPullback`), and restriction
along `j_y` does not depend on `y` (`AlgebraicGeometry.Etale.pullbackLiftSectionRestrict_eq`):
by proper base change it is evaluation of global sections at the point `y`, which is determined
by `H^0(X, Λ) = Λ` (`AlgebraicGeometry.Etale.injective_comp_unit_tateObject_shift`).

In codimension `d = 0` a regular immersion is an isomorphism
(`AlgebraicGeometry.IsRegularImmersion.isIso_of_zero`) and there is only one point.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] HasInvertibleExponent.opens

section Coherence

variable {Λ : Type (u + 1)} [CommRing Λ] [HasTateTwist Λ] {X S : Scheme.{u}} (a : X ⟶ S)

end Coherence

section PointClass

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} [HasInvertibleExponent Λ X] {d : ℕ}
  (a : X ⟶ Spec (.of k)) [IsProper a] [SmoothOfRelativeDimension d a]

end PointClass

end Etale

end AlgebraicGeometry
