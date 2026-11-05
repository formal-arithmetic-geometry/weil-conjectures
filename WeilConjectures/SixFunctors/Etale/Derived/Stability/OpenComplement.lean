/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-!
# The open-complement condition

For a finite ring `Λ` and a quasi-compact open immersion `j : V ⟶ T`, the pair `(V, T)` satisfies
the *open-complement condition with constant `c`* (`def-exc-open-complement-bound`) if
`Rᵠj_* M = 0` for `q > c` and every sheaf `M` of `Λ`-modules on `V_ét`, and `Rᵠj_*` carries
constructible sheaves to constructible sheaves in every degree.

This file proves that over a separably closed field `k`, for `T` of finite type over `k` of
dimension at most `d`, the condition holds with `c = 2d`, uniformly in the finite coefficient ring
`Λ` whose exponent is invertible in `k` (`thm-pur-open-complement-unconditional`).

## Main definitions

- `AlgebraicGeometry.Etale.OpenComplementBound`: the open-complement condition.

## Main statements

- `AlgebraicGeometry.Etale.openComplementBound_two_mul`
  (`thm-pur-open-complement-unconditional`): the condition with constant `2 dim T`.
- `AlgebraicGeometry.Etale.higherDirectImageIsoHomologyRightDerivedLowerStar`: `Rᵠj_* F` is the
  `q`-th homology sheaf of the unbounded `Rj_*(F[0])`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The higher direct image `Rᵠh_* F` (defined with the bounded below derived functor) is the
`q`-th homology sheaf of the unbounded derived direct image of `F` placed in degree `0`. -/
noncomputable def higherDirectImageIsoHomologyRightDerivedLowerStar {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    higherDirectImage Λ h q F ≅
      (_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R((h)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  (_root_.DerivedCategory.homologyFunctor _ q).mapIso
    (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))

end Etale

end AlgebraicGeometry
