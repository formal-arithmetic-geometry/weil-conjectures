/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.ZModCoefficients

/-!
# Global sections of pulled back constant sheaves of `ℤ/ℓ`-modules

Let `u : W' ⟶ W` be a morphism of schemes. The global sections of the pullback of the constant
sheaf `ℤ/ℓ` along `u` are `ℤ/ℓ` as soon as `W'` is nonempty and connected; and for a closed
immersion `i : D ⟶ W`, the global sections over `W'` of the pullback of `i_* ℤ/ℓ` are `ℤ/ℓ` as
soon as `D ×_W W'` is nonempty and connected (closed base change in degree zero).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_upperStar_lowerStar_constantZModModule_of_isPullback`
- `AlgebraicGeometry.Etale.nonempty_addEquiv_sections_upperStar_constantZModModule`
- `AlgebraicGeometry.Etale.nonempty_addEquiv_sections_upperStar_lowerStar_constantZModModule`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- **Closed base change in degree zero for constant sheaves.** For a cartesian square with a
closed immersion `i : D ⟶ W` and any `u : W' ⟶ W`, `u^* i_* ℤ/ℓ ≅ i'_* ℤ/ℓ`. -/
theorem nonempty_iso_upperStar_lowerStar_constantZModModule_of_isPullback
    {W W' D D' : Scheme.{u}} (u : W' ⟶ W) (i : D ⟶ W) [IsClosedImmersion i] (i' : D' ⟶ W')
    (u' : D' ⟶ D) (sq : IsPullback u' i' i u) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty ((u)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj
        ((i)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D ℓ)) ≅
      (i')_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D' ℓ)) := by
  sorry

/-- The global sections over a nonempty connected scheme `W'` of the pullback along any
`u : W' ⟶ W` of the constant sheaf `ℤ/ℓ` are `ℤ/ℓ`. -/
theorem nonempty_addEquiv_sections_upperStar_constantZModModule {W W' : Scheme.{u}}
    (u : W' ⟶ W) [ConnectedSpace W'] (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty ((sectionsFunctor (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) W').obj
      ((u)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule W ℓ)) ≃+ ZMod ℓ) := by
  sorry

/-- The global sections over `W'` of the pullback along `u : W' ⟶ W` of `i_* ℤ/ℓ`, for a closed
immersion `i : D ⟶ W`, are `ℤ/ℓ` when `D ×_W W'` is nonempty and connected. -/
theorem nonempty_addEquiv_sections_upperStar_lowerStar_constantZModModule
    {W W' D : Scheme.{u}} (u : W' ⟶ W) (i : D ⟶ W) [IsClosedImmersion i]
    [ConnectedSpace (Limits.pullback i u : Scheme.{u})] (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty ((sectionsFunctor (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) W').obj
      ((u)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj
        ((i)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule D ℓ))) ≃+
      ZMod ℓ) := by
  sorry

end AlgebraicGeometry.Etale
