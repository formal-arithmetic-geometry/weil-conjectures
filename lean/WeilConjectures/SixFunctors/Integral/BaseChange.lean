/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Integral.Exact

import Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

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
finite case is `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`.

The Lean proof reduces to the geometric-point exchange, applies it to the base-changed
integral morphism and to the outer square, and cancels the two comparison isomorphisms
in the horizontal pasting identity. The inverse-image stalk isomorphism then makes
every geometric stalk of the original exchange invertible.
Source: Stacks Project, Tag 0EYP.
(blueprint: lem-sbc-integral-underived-exchange). -/
theorem Etale.isIso_baseChangeMap_of_isIntegralHom (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have hf' : IsIntegralHom f' := MorphismProperty.of_isPullback sq inferInstance
  suffices ∀ F, IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) from
    NatIso.isIso_of_isIso_app _
  intro F
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun y ↦ ?_
  let s := Y'.algClosurePoint y
  -- Compare the inner and outer exchanges over the same geometric point.
  let sq₂ := IsPullback.of_hasPullback f' s
  have sq₃ := sq₂.paste_horiz sq
  have h₂ := Etale.isIso_baseChangeMap_app_of_isIntegralHom_geometricPoint Λ sq₂
    ((g')^*[ModuleCat.{u + 1} Λ].obj F)
  have h₃ := Etale.isIso_baseChangeMap_app_of_isIntegralHom_geometricPoint Λ sq₃ F
  have hp := Etale.baseChangeMap_paste_horiz_app (ModuleCat.{u + 1} Λ)
    sq.toCommSq sq₂.toCommSq sq₃.toCommSq F
  -- Pasting isolates the pullback of the exchange we want to prove.
  have hs : IsIso ((s)^*[ModuleCat.{u + 1} Λ].map
      ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)) := by
    rw [hp] at h₃
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h₃
  -- Pullback to s followed by its identity-point stalk is the original stalk.
  have hi := Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) s
    (𝟙 (Spec (.of (AlgebraicClosure (Y'.residueField y)))))
  rw [Category.id_comp] at hi
  rw [Scheme.uliftPointSmallEtale, ← NatIso.isIso_map_iff hi]
  change IsIso (((Scheme.pointSmallEtale _).ulift.{u + 1}).sheafFiber.map
    ((s)^*[ModuleCat.{u + 1} Λ].map
      ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)))
  infer_instance

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
