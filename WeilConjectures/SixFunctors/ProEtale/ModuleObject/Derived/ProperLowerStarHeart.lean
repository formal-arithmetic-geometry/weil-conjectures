/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# The heart hypotheses for the derived direct image of module objects

Let `Λ` be a commutative condensed ring, flat over `ℤ`, and `f : X ⟶ Y` a quasi-compact
quasi-separated morphism of schemes. We show that the derived direct image `Rf_*` of module
objects over `Λ` commutes with direct sums of module objects placed in degree `0` (blueprint
`sk-cor-pe-bounded-continuity`), and that a bound `Rf_*(N[0]) ∈ D^{≤ d}` for the objects `N` of a
class `P` extends to filtered colimits of objects of `P`. Both follow from the continuity of the
higher direct images of abelian sheaves
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`), the higher direct
images of module objects being computed on the underlying abelian sheaves.

We deduce the hypotheses `ProperLowerStarHeartHypotheses` from the ind-constructible heart and a
uniform bound on constructible module objects (blueprints `sk-lem-proper-heart-bound`,
`det-prop-int-compactness-direct-sums` (1), formal part).

## Main results

All in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`:

* `isIso_sigmaComparison_rightDerivedLowerStar_singleFunctor`:
  `Rf_*` commutes with direct sums of module objects placed in degree `0`.
* `isLE_rightDerivedLowerStar_singleFunctor_of_ind`:
  degree bounds for `Rf_*` pass to filtered colimits.
* `properLowerStarHeartHypotheses_of_isIndConstructibleHeart`:
  the heart hypotheses follow from the ind-constructible heart and a uniform bound.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace DerivedCategory

variable {A : Type*} [Category* A] {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] {J : Type*} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) (DerivedCategory C)]

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions D] [HasColimitsOfShape (Discrete J) D]
  [HasExactColimitsOfShape (Discrete J) D] [HasColimitsOfShape (Discrete J) (DerivedCategory D)]
  [EnoughInjectives C]

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Forget

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

variable [QuasiCompact f] [QuasiSeparated f]

end Forget

end AlgebraicGeometry.ProEtale.CondensedRing
