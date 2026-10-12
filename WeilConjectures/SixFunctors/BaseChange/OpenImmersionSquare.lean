/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open-immersion squares

An *open-immersion square* is a cartesian square of schemes

```
  U' --g_U--> U
  |           |
  j'          j
  ↓           ↓
  X' ---g---> X
```

in which `j` is an open immersion; then `j'`, a base change of `j`, is an open immersion as
well, so that `U' = U ×_X X'` is the preimage of `U` in `X'`. No hypothesis is made on `g`.

## Main definitions

- `AlgebraicGeometry.IsOpenImmersionSquare`: the predicate on a commutative square.

## Main results

- `AlgebraicGeometry.IsOpenImmersionSquare.isOpenImmersion_left`: the base change `j'` of `j`
  is an open immersion.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {U' U X' X : Scheme.{u}}

/-- An *open-immersion square*: a cartesian square `g_U ≫ j = j' ≫ g` of schemes in which
`j : U ⟶ X` is an open immersion. The base change `j' : U' ⟶ X'` of `j` along `g` is then an
open immersion as well (`AlgebraicGeometry.IsOpenImmersionSquare.isOpenImmersion_left`), and
no hypothesis is made on `g`. (blueprint: `def-cbc-open-immersion-square`) -/
structure IsOpenImmersionSquare (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X) : Prop
    extends IsPullback gU j' j g where
  isOpenImmersion_right : IsOpenImmersion j

namespace IsOpenImmersionSquare

variable {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}

/-- In an open-immersion square, the base change `j' : U' ⟶ X'` of the open immersion `j` is
an open immersion. -/
lemma isOpenImmersion_left (h : IsOpenImmersionSquare gU j' j g) : IsOpenImmersion j' :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.toIsPullback
    h.isOpenImmersion_right

end IsOpenImmersionSquare

end AlgebraicGeometry
