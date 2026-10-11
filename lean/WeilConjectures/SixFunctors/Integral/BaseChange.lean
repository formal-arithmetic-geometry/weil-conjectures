/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Integral.Exact

/-!
# Base change along an integral morphism

For a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `f` integral, the base change map `g^* f_* ⟶ f'_* g'^*` on étale sheaves of `Λ`-modules is
an isomorphism (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom`). As `f_*` and
`f'_*` are exact, the derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on `D⁺` is then an
isomorphism as well (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom`).
This extends the finite case `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom`: base change along an
  integral morphism.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom`: its derived form.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} [IsIntegralHom f]

/-- **Base change along an integral morphism**: for a cartesian square with `f` integral, the
base change map `g^* f_* ⟶ f'_* g'^*` on étale sheaves of `Λ`-modules is an isomorphism.

It is checked on the stalks at the geometric points of `Y'`. For an integral morphism the
stalk of `f_* F` at a geometric point `y` of `Y` is the module of sections of `F` over
`X ×_Y Spec 𝒪^{sh}_{Y,y}`, the spectrum of an integral algebra over a strictly henselian local
ring, and such sections only depend on the fibre of `X` over `y`, which is the same for `y` and
for a geometric point of `Y'` above it. This is the integral case of the exchange property whose
finite case is `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`. -/
theorem Etale.isIso_baseChangeMap_of_isIntegralHom (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  sorry

/-- **Derived base change along an integral morphism**: for a cartesian square with `f`
integral, the derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on `D⁺` is an isomorphism. The
pushforwards along `f` and along its base change `f'`, which is integral too, are exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`), so this follows
from the sheaf-level statement
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom` without resolutions. -/
theorem Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have : IsIntegralHom f' := MorphismProperty.of_isPullback sq inferInstance
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ f
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ f'
  have := Etale.isIso_baseChangeMap_of_isIntegralHom Λ sq
  exact Etale.isIso_derivedBaseChangeMapPlus_of_isIso_baseChangeMap _ sq.toCommSq

end AlgebraicGeometry
