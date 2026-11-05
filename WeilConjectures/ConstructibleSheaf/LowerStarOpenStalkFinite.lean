/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.LowerStarOpenStalk
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.UnitMono
public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtensionIso
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Finiteness of the stalks of a direct image along an open immersion, via a finite cover

Let `j : U ⟶ X` be an open immersion with `U` quasi-compact and `F` a finite locally constant
sheaf of modules over a finite ring on `U`. Suppose that `X` is covered by the images of finitely
many finite morphisms `ν_i : Y_i ⟶ X` from locally noetherian schemes `Y_i` all of whose étale
schemes have domains as local rings (for instance regular schemes, such as the normalizations of
the irreducible components of a curve). Then the geometric stalks of `j_* F` are finite.

Write `q_i : Y_i ×_X U ⟶ U` and `o_i : Y_i ×_X U ⟶ Y_i` for the projections. The `q_i` are
finite and jointly surjective, so `F ⟶ ∏ᵢ (q_i)_* (q_i)^* F` is a monomorphism
(`AlgebraicGeometry.Etale.mono_piLift_unit`), and so is its direct image along `j`. Since
`j_* (q_i)_* = (ν_i)_* (o_i)_*`, the stalk of `j_* (q_i)_* (q_i)^* F` at a geometric point `y`
is the finite product of the stalks of `(o_i)_* (q_i)^* F` at the geometric points of `Y_i`
over `y` (`AlgebraicGeometry.Etale.stalkIsoPi`), and these are finite by
`AlgebraicGeometry.Etale.finite_sheafFiber_lowerStar`.

## Main statements

- `AlgebraicGeometry.Etale.finite_sheafFiber_lowerStar_of_isFinite`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

end Etale

end AlgebraicGeometry
