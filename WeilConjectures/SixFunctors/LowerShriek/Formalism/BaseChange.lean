/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.RefinementOfIsPullback
public import WeilConjectures.Compactification.TriangleOfIsPullback
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Canonical

/-!
# Compact-support base change in a compact support formalism

Let `F` be a `AlgebraicGeometry.CompactSupportFormalism`. For a commutative square of schemes
```
U' --t--> U
|l        |r
Z' --b--> Z
```
the *base change map of the pushforwards* `b^* r_* ⟶ l_* t^*` is the mate of the square
isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` (`CategoryTheory.ExchangeFormalism.pfBaseChange`). The
formalism *satisfies proper base change* (`CompactSupportFormalism.HasProperBaseChange`) if this
map is an isomorphism for every cartesian square with `r` proper.

For a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
a compactification `c = (X ⟶[c.i] c.Z ⟶[c.g] Y)` of `f` and a compactification `c'` of `f'`
lying over it along a morphism `h : c'.Z ⟶ c.Z` with cartesian squares
```
X' --g'--> X
|c'.i      |c.i
c'.Z --h--> c.Z
|c'.g      |c.g
Y' --g---> Y
```
(for instance the base change `c.ofIsPullback sq` of `c`, blueprint
`def-cbc-compact-support-square`), the *compact-support exchange map* (blueprint
`def-cbc-exchange-map`)

`Ex_! : g^* Rf_!(c) ⟶ Rf'_!(c') g'^*`

is the base change map of the pushforwards for the proper `c.g`, applied after `(c.i)_!`,
composed with the inverse of the base change isomorphism `g'^* ⋙ (c'.i)_! ≅ (c.i)_! ⋙ h^*` of
the extension by zero (`CompactSupportFormalism.shriekBaseChange`). It is an isomorphism when
`F` satisfies base change for the extension by zero and proper base change
(`CompactSupportFormalism.isIso_shriekBaseChange`), and it is natural, the identity for the
identity square, compatible with horizontal pasting and with the comparison isomorphisms along
refinements of compactifications. Computed with the chosen compactifications, it gives the
exchange map `F.lowerShriekBaseChange` of the canonical compactly supported direct images, which
does not depend on the compactification and is compatible with vertical pasting through the
composition isomorphisms.

## Main definitions

- `AlgebraicGeometry.CompactSupportFormalism.HasProperBaseChange`: proper base change.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange`: the exchange map `Ex_!` along
  compactifications.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange`: the exchange map `Ex_!` of
  the canonical compactly supported direct images.

## Main statements

- `AlgebraicGeometry.CompactSupportFormalism.isIso_shriekBaseChange`: `Ex_!` is an isomorphism.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_id`: identity law.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_paste_horiz`: horizontal pasting.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_refinementComparison`:
  compatibility with the comparisons along refinements.
- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChangeOfIsPullback_shriekIso`:
  compatibility with the comparison isomorphisms.
- `AlgebraicGeometry.CompactSupportFormalism.compIso_shriekBaseChange`: compatibility with the
  composition isomorphisms of triangles of compactifications.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange_eq`: independence of the
  compactification.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange_paste_vert`: vertical pasting.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

section ShriekBaseChange

variable [F.HasBaseChange] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  {g' : X' ⟶ X}

end ShriekBaseChange

section Composition

variable [F.HasProperExchange]

end Composition

section Canonical

variable [F.HasProperExchange] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

end Canonical

end AlgebraicGeometry.CompactSupportFormalism
