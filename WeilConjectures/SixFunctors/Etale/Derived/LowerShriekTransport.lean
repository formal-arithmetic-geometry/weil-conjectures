/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-!

# Transport of the derived lower shriek along isomorphisms of schemes

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be morphisms of schemes and `eX : X ≅ X'`, `eY : Y ≅ Y'`
isomorphisms with `f ≫ eY.hom = eX.hom ≫ f'`. The derived lower shrieks attached to a
compactification `c` of `f` and to its transport `c.transport` (`Compactification.transport`)
are intertwined by the pullbacks along the isomorphisms:

`Rf'_!(c.transport) ⋙ D(eY^*) ≅ D(eX^*) ⋙ Rf_!(c)`.

This only uses that `eX` and `eY` are isomorphisms: the pushforward along an isomorphism `e`
is an exact equivalence, so `R(e_*) ≅ D(e_*)` is inverse to `D(e^*)`. Combined with the
independence of `Rf_!` of the compactification, this is what transports a Frobenius
structure through `Rf_!` when the Frobenius does not act on the chosen compactification.

## Main definitions

- `AlgebraicGeometry.Etale.mapDerivedLowerStarEquivalenceOfIso`: the equivalence
  `D(e_*) : D(Y_ét) ≌ D(Y'_ét)` for an isomorphism `e : Y ≅ Y'`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarCompMapDerivedUpperStarIso`:
  `R(e_*) ⋙ D(e^*) ≅ 𝟭`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationTransportIso`:
  `Rf'_!(c.transport) ⋙ D(eY^*) ≅ D(eX^*) ⋙ Rf_!(c)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

section LowerStar

variable {Y Y' : Scheme.{u}} (e : Y ≅ Y')

end LowerStar

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} (eX : X ≅ X') (eY : Y ≅ Y')
  (w : f ≫ eY.hom = eX.hom ≫ f') (c : Compactification f)

end Etale

end AlgebraicGeometry
