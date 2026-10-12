/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonMate

/-!
# Transport identifies the exchange map

Conjugating the étale exchange map `g^* Rf_* ⟶ Rf'_* g'^*` of a square by the comparison
isomorphisms of `WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonIso` gives the
pro-étale exchange map (blueprint `lem-weil-pbc-transport-identifies-exchange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-weil-pbc-transport-identifies-exchange` (subsection
`sk-thm-properbasechange`): for a Cartesian square

```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```

with `f` (hence `f'`) quasi-compact and quasi-separated, and `L ∈ D⁺(X_ét, Λ)`, conjugating
the étale exchange map `g^* Rf_* L ⟶ Rf'_* g'^* L` by the comparison isomorphisms
`ν_{Y'}^* g^* Rf_* L ≅ Lg^* Rf_* ν_X^* L` and `ν_{Y'}^* Rf'_* g'^* L ≅ Rf'_* Lg'^* ν_X^* L`
(`AlgebraicGeometry.ProEtale.baseChangeSourceComparisonIso`,
`AlgebraicGeometry.ProEtale.baseChangeTargetComparisonIso`) gives the pro-étale exchange map
at `ν_X^* L`. -/
theorem comparison_derivedBaseChangeMap [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f']
    [QuasiSeparated f'] (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(Y')[ModuleCat.{u + 1} Λ]).map
        (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L)) ≫
      (baseChangeTargetComparisonIso g' f' Λ).hom.app L =
    (baseChangeSourceComparisonIso f g Λ).hom.app L ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj L)) :=
  sorry

end ProEtale

end AlgebraicGeometry
