/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BoundedAmplitudeCoproducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# The pro-étale direct image of bounded amplitude preserves coproducts

Let `p : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes and `A` a Grothendieck
abelian coefficient category. On the small pro-étale sites, the direct image `p_*` commutes
with coproducts and coproducts of injective sheaves are `p_*`-acyclic, the cohomology of the
quasi-compact quasi-separated objects `X ×_Y V` (`V` affine) commuting with direct sums.

Consequently, if `Rp_*` has bounded cohomological amplitude on sheaves, then `Rp_*` preserves
coproducts on the unbounded derived categories
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerivedLowerStar_of_isZero`); this
is the homological part of blueprint `sk-prop-sf-existence` (b).

## Main statements

- `AlgebraicGeometry.ProEtale.preservesColimitsOfShape_lowerStar`
- `AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_injective`
- `AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerivedLowerStar_of_isZero`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- Pro-étale sheaves with values in a Grothendieck abelian category have K-injective
resolutions. -/
local instance : Abelian.HasKInjectiveResolutions (Sheaf (Scheme.ProEt.topology X) A) :=
  Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}

/-- Pro-étale sheaves with values in a Grothendieck abelian category have small coproducts. -/
local instance (K : Type (u + 1)) :
    HasColimitsOfShape (Discrete K) (Sheaf (Scheme.ProEt.topology X) A) :=
  have := IsGrothendieckAbelian.hasColimits (Sheaf (Scheme.ProEt.topology X) A)
  inferInstance

/-- The pro-étale direct image along a quasi-compact quasi-separated morphism preserves
coproducts: on an affine `V`, the sections of a coproduct over the quasi-compact
quasi-separated `X ×_Y V` are the coproduct of the sections. -/
theorem preservesColimitsOfShape_lowerStar [QuasiCompact p] [QuasiSeparated p]
    (K : Type (u + 1)) : PreservesColimitsOfShape (Discrete K) (p)_*[A] :=
  sorry

/-- Coproducts of injective pro-étale sheaves are acyclic for the direct image along a
quasi-compact quasi-separated morphism: the higher cohomology of a coproduct of injective
sheaves vanishes on the quasi-compact quasi-separated objects `X ×_Y V` (`V` affine). -/
theorem rightAcyclic_lowerStar_of_injective [QuasiCompact p] [QuasiSeparated p]
    {K : Type (u + 1)} (G : Discrete K ⥤ Sheaf (Scheme.ProEt.topology X) A)
    (hG : ∀ j, Injective (G.obj j)) (c : Cocone G) (hc : IsColimit c) :
    (p)_*[A].rightAcyclic c.pt :=
  sorry

/-- If the pro-étale `Rp_*` along a quasi-compact quasi-separated `p` has cohomological
amplitude at most `N` on sheaves, then `Rp_*` preserves coproducts on the unbounded derived
categories (blueprint `sk-prop-sf-existence` (b), proof): the bound makes `Rp_*` computed by
complexes of `p_*`-acyclic sheaves, such as coproducts of complexes of injective sheaves, and
`p_*` preserves coproducts. -/
theorem preservesColimitsOfShape_rightDerivedLowerStar_of_isZero [QuasiCompact p]
    [QuasiSeparated p] (N : ℕ)
    (h : ∀ (F : Sheaf (Scheme.ProEt.topology X) A) (r : ℤ), (N : ℤ) < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((R((p)_*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj F))))
    (K : Type (u + 1)) : PreservesColimitsOfShape (Discrete K) (R((p)_*[A])) :=
  have := preservesColimitsOfShape_lowerStar A p K
  Functor.preservesColimitsOfShape_discrete_rightDerivedFunctor_of_isZero.{u + 1} _ K N h
    fun G hG c hc ↦ rightAcyclic_lowerStar_of_injective A p G hG c hc

end ProEtale

end AlgebraicGeometry
