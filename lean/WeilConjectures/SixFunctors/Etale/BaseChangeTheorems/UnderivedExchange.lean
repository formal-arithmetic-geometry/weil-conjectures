/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import Sheaf.AlgebraicGeometry.ProperGeometricPointExchange
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# The underived proper base change

For a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the underived base change map `g^* f_* F ⟶ f'_* g'^* F` of
`AlgebraicGeometry.Etale.baseChangeMap` is an isomorphism for every étale sheaf `F` of
`Λ`-modules on `X`. At a geometric point `ȳ'` of `Y'` lying over the geometric point `ȳ` of
`Y`, both stalks are the sections of `F` over the same closed geometric fibre
`X_ȳ = X'_ȳ'`: the stalk of `f_* F` at `ȳ` is `Γ(X ×_Y Y_(ȳ), F|)` over the strict
henselisation, which is `Γ(X_ȳ, F|)` by the degree-zero comparison over a strictly henselian
base, and likewise for `f'`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`: the underived proper base change.

## References

- Stacks Project, Lemma 59.91.5, <https://stacks.math.columbia.edu/tag/0A3T>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The underived proper exchange is an isomorphism**: for a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base change map `g^* f_* F ⟶ f'_* g'^* F` is an isomorphism for every
étale sheaf `F` of `Λ`-modules on `X`. At a geometric point `ȳ'` of `Y'` both stalks are the
sections of `F` over the closed geometric fibre `X_ȳ = X'_ȳ'`, by the stalk formula over the
strict henselisation and the degree-zero comparison
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre`, and the induced
map of stalks is the identity; geometric stalks are conservative.
(blueprint: `lemma-weil-pbc-proper-underived-exchange`) -/
@[stacks 0A3T]
theorem Etale.isIso_baseChangeMap_of_isProper {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsProper f] :
    IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have hf' : IsProper f' := MorphismProperty.of_isPullback sq (inferInstance : IsProper f)
  suffices ∀ F, IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) from
    NatIso.isIso_of_isIso_app _
  intro F
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun y ↦ ?_
  let s := Y'.algClosurePoint y
  let sq₂ := IsPullback.of_hasPullback f' s
  have sq₃ := sq₂.paste_horiz sq
  have h₂ := Etale.isIso_baseChangeMap_app_of_isProper_geometricPoint Λ sq₂
    ((g')^*[ModuleCat.{u + 1} Λ].obj F)
  have h₃ := Etale.isIso_baseChangeMap_app_of_isProper_geometricPoint Λ sq₃ F
  have hp := Etale.baseChangeMap_paste_horiz_app (ModuleCat.{u + 1} Λ)
    sq.toCommSq sq₂.toCommSq sq₃.toCommSq F
  have hs : IsIso ((s)^*[ModuleCat.{u + 1} Λ].map
      ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)) := by
    rw [hp] at h₃
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h₃
  rw [Scheme.uliftPointSmallEtale,
    NatIso.isIso_map_iff ((Scheme.pointSmallEtale _).uliftSheafFiberIso _)]
  have hi := Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s
    (𝟙 (Spec (.of (AlgebraicClosure (Y'.residueField y)))))
  rw [Category.id_comp] at hi
  rw [← NatIso.isIso_map_iff hi]
  change IsIso ((Scheme.pointSmallEtale _).sheafFiber.map
    ((s)^*[ModuleCat.{u + 1} Λ].map
      ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)))
  infer_instance

end AlgebraicGeometry
