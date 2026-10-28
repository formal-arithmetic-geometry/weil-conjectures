/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection

/-!
# The unit of the étale extension by zero is compatible with the projection map

Let `e : X ⟶ Y` be étale with a compactification `c`. The candidate unit
`η : 𝟭 ⟶ Rf_!(c) ⋙ Le^*` (`AlgebraicGeometry.Etale.compactificationEtaleUnit`) is compatible
with the projection map `PF_c : Rf_!(c)M ⊗ᴸ N ⟶ Rf_!(c)(M ⊗ᴸ Le^*N)`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification`): at `M ⊗ᴸ Le^*N` it is `η_M ⊗ᴸ 𝟙`
followed by the tensor comparison of `Le^*` and `Le^*` of the projection map
(`AlgebraicGeometry.Etale.compactificationEtaleUnit_tensor`).

## Main statements

- `AlgebraicGeometry.Etale.compactificationEtaleUnit_tensor`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

/-- **The unit of `Rf_!(c) ⊣ Le^*` is compatible with the projection map**: for `M` on `X` and
`N` on `Y`, the unit at `M ⊗ᴸ Le^*N` is the unit at `M` tensored with `Le^*N`, followed by the
tensor comparison `Le^*(Rf_!(c)M) ⊗ᴸ Le^*N ≅ Le^*(Rf_!(c)M ⊗ᴸ N)` and `Le^*` of the projection
map `Rf_!(c)M ⊗ᴸ N ⟶ Rf_!(c)(M ⊗ᴸ Le^*N)`. -/
theorem compactificationEtaleUnit_tensor
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleUnit Λ e c).app
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj M).obj (L((e)^*[ModuleCat.{u + 1} Λ]).obj N)) =
      ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map ((compactificationEtaleUnit Λ e c).app M)).app
          (L((e)^*[ModuleCat.{u + 1} Λ]).obj N) ≫
        (leftDerivedUpperStarTensorIso _ e (Rf_!(c)[ModuleCat.{u + 1} Λ].obj M) N).inv ≫
        L((e)^*[ModuleCat.{u + 1} Λ]).map
          (((projectionMapOfCompactification _ c).app M).app N) :=
  sorry

end Etale

end AlgebraicGeometry
