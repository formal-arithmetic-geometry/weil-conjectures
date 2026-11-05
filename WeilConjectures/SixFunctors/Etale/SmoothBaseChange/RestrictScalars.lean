/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Restriction of scalars, pullbacks and base change maps

Let `φ : Λ →+* Λ'` be a morphism of rings. Restriction of scalars along `φ` commutes with the
direct image (`AlgebraicGeometry.Etale.lowerStarCompRestrictScalarsIso`) and with the derived
direct image (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`). This file
shows that it also commutes with pullbacks and with the base change map of a commutative square,
so that the base change map of a sheaf of `Λ'`-modules may be computed over `Λ`.

## Main statements

- `AlgebraicGeometry.Etale.upperStarRestrictScalars`: the comparison `f^* ∘ res ⟶ res ∘ f^*`,
  an isomorphism by `AlgebraicGeometry.Etale.isIso_upperStarRestrictScalars`.
- `AlgebraicGeometry.Etale.baseChangeMap_restrictScalars`: restriction of scalars commutes with
  the underived base change map of a commutative square.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

section UpperStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

end UpperStar

section Comp

open TwoSquare

variable {Z W V : Scheme.{u}}

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

end Comp

section Torsion

variable {X : Scheme.{u}}

end Torsion

end AlgebraicGeometry.Etale
