/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-!
# The stalk of a compactly supported direct image

Let `π : E ⟶ B` be a morphism admitting a compactification, `Λ` a finite ring and
`b̄ : Spec Ω ⟶ B` a geometric point, with fibre `E_b̄ = E ×_B Spec Ω`. The stalk of `Rπ_! K` at
`b̄` is the compactly supported cohomology of the fibre:

`Lb̄^*(Rπ_! K) ≅ R(π_b̄)_!(K|_{E_b̄})`, hence `RΓ(Spec Ω, Lb̄^*(Rπ_! K)) ≅ RΓ_c(E_b̄, K|_{E_b̄})`.

Both are instances of compact-support base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`).

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap_app_point`
  (`lem-pur-cfiber-stalk`): the comparison map is an isomorphism.
- `AlgebraicGeometry.Etale.pointRightDerivedLowerShriekIso`: the isomorphism
  `Lb̄^*(Rπ_! K) ≅ R(π_b̄)_!(K|_{E_b̄})`.
- `AlgebraicGeometry.Etale.pointRightDerivedLowerShriekGlobalSectionsIso`: the isomorphism
  `RΓ(Spec Ω, Lb̄^*(Rπ_! K)) ≅ RΓ_c(E_b̄, K|_{E_b̄})`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {E B E' : Scheme.{u}} {π : E ⟶ B}
  [HasCompactification π] {Ω : Type u} [Field Ω] {b : Spec (.of Ω) ⟶ B}
  {g' : E' ⟶ E} {π' : E' ⟶ Spec (.of Ω)}
  [HasCompactification π'] [QuasiCompact π']

/-- Blueprint `lem-pur-cfiber-stalk`: stalk of the compactly supported direct image.

Let `π : E ⟶ B` admit a compactification (e.g. `π` separated of finite type over a
noetherian base), let `Λ` be a finite ring, and let `b̄ : Spec Ω ⟶ B` be a point, with fibre
square

```
  E_b̄ --g'--> E
   |          |
   π'         π
   ↓          ↓
 Spec Ω --b̄--> B
```

For every `K ∈ D(E_ét, Λ)` the canonical comparison (compact-support base change)

`Lb̄^*(Rπ_! K) ⟶ R(π')_!(Lg'^* K)`

is an isomorphism in `D((Spec Ω)_ét, Λ)`. The hypotheses that `π'` is quasi-compact and admits a
compactification hold if `π` is quasi-compact (`MorphismProperty.of_isPullback`,
`AlgebraicGeometry.HasCompactification.of_isPullback`). For a geometric point (`Ω` separably
closed), `Lb̄^*(Rπ_! K)` is the stalk `(Rπ_! K)_b̄` and `R(π')_!(Lg'^* K)` computes
`RΓ_c(E_b̄, K|_{E_b̄})` (`AlgebraicGeometry.Etale.pointRightDerivedLowerShriekGlobalSectionsIso`).
Neither the boundedness and constructibility of `K` nor the separable closedness of `Ω` is
needed. -/
theorem isIso_rightDerivedLowerShriekBaseChangeMap_app_point (sq : IsPullback g' π' π b)
    (K : DerivedCategory (Sheaf E.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  inferInstance

/-- The stalk of `Rπ_! K` at a point `b̄ : Spec Ω ⟶ B` is the compactly supported direct image of
the restriction of `K` to the fibre: `Lb̄^*(Rπ_! K) ≅ R(π')_!(Lg'^* K)`
(`lem-pur-cfiber-stalk`,
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap_app_point`). -/
noncomputable def pointRightDerivedLowerShriekIso (sq : IsPullback g' π' π b)
    (K : DerivedCategory (Sheaf E.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((b)^*[ModuleCat.{u + 1} Λ]).obj (R(π)_![ModuleCat.{u + 1} Λ].obj K) ≅
      R(π')_![ModuleCat.{u + 1} Λ].obj (L((g')^*[ModuleCat.{u + 1} Λ]).obj K) :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap_app_point Λ sq K
  asIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K)

/-- `RΓ(Spec Ω, (Rπ_! K)_b̄) ≅ RΓ_c(E_b̄, K|_{E_b̄})`: the derived global sections of the stalk
of `Rπ_! K` at a point `b̄ : Spec Ω ⟶ B` are the compactly supported cohomology of the fibre
(`lem-pur-cfiber-stalk`). For `Ω` separably closed, `RΓ(Spec Ω, -)` is the stalk at the unique
geometric point. -/
noncomputable def pointRightDerivedLowerShriekGlobalSectionsIso (sq : IsPullback g' π' π b)
    (K : DerivedCategory (Sheaf E.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
        (L((b)^*[ModuleCat.{u + 1} Λ]).obj (R(π)_![ModuleCat.{u + 1} Λ].obj K)) ≅
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) π').obj
        (L((g')^*[ModuleCat.{u + 1} Λ]).obj K) :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).mapIso
    (pointRightDerivedLowerShriekIso Λ sq K)

end Etale

end AlgebraicGeometry
