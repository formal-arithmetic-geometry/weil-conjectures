/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualProper
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
# The double-dual morphism and the Verdier exchange for a proper push-forward

For a proper `f : X ⟶ Y`, a finite coefficient ring `Λ` and an isomorphism
`γ : Rf^! ω_Y ≅ ω_X`, the canonical exchange morphism `Rf_* 𝔻_X M ⟶ 𝔻_Y Rf_* M` is the dual
comparison (`CategoryTheory.MonoidalClosed.dualComparison`)
`Rf_* RHom(M, ω_X) ⟶ RHom(Rf_* M, Rf_* ω_X) ⟶ RHom(Rf_* M, ω_Y)`, through the lax monoidal
structure of `Rf_*` and the trace `Rf_* ω_X ≅ Rf_* Rf^! ω_Y ⟶ ω_Y`. It is an isomorphism
(`AlgebraicGeometry.Etale.isIso_dualComparison_rightDerivedLowerStar`), the inverse direction of
the exchange `(10.3)` `𝔻_Y Rf_! ≅ Rf_* 𝔻_X` (`Rf_! = Rf_*`), and it satisfies
the compatibility with the double-dual morphisms of blueprint
`lemma-internal-adjunction-two-exchange-formulas--4`
(`AlgebraicGeometry.Etale.rightDerivedLowerStar_map_toIhomIhom_comp_dualComparison`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal
  Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} (aX : X ⟶ S)
  (aY : Y ⟶ S) [HasCompactification aX] [HasCompactification aY]
  (f : X ⟶ Y) [IsProper f] [HasCompactification f]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- The lax braided structure of `Rf_*`, as the right adjoint of the braided monoidal `Lf^*`. -/
@[instance_reducible]
noncomputable def rightDerivedLowerStarLaxBraided :
    (R((f)_*[ModuleCat.{u + 1} Λ])).LaxBraided :=
  letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) f
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).rightAdjointLaxBraidedOfδ
    (leftDerivedUpperStar_map_braiding_hom_δ (ModuleCat.{u + 1} Λ) f)

/-- The canonical Verdier exchange morphism `Rf_* 𝔻_X M ⟶ 𝔻_Y Rf_* M` of a proper `f` is an
isomorphism. For `γ : Rf^! ω_Y ≅ ω_X`, it is the dual comparison
`Rf_* RHom(M, ω_X) ⟶ RHom(Rf_* M, Rf_* ω_X) ⟶ RHom(Rf_* M, ω_Y)`
(`CategoryTheory.MonoidalClosed.dualComparison`) through the lax monoidal structure of `Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarLaxBraided`) and the trace
`Rf_* ω_X ≅ Rf_* Rf^! ω_Y ⟶ ω_Y` (the counit of `Rf_* ≅ Rf_! ⊣ Rf^!`); it is an isomorphism by
the projection formula for `Rf_*`
(`CategoryTheory.Adjunction.isIso_dualComparison_of_isIso_projection`). -/
theorem isIso_dualComparison_rightDerivedLowerStar
    (γ : (R(f)^![Λ]).obj (dualizingComplex Λ aY) ≅ dualizingComplex Λ aX)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := rightDerivedLowerStarLaxBraided Λ f
    IsIso (dualComparison (R((f)_*[ModuleCat.{u + 1} Λ]))
      ((R((f)_*[ModuleCat.{u + 1} Λ])).map γ.symm.hom ≫
        ((rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f)).counit.app
          (dualizingComplex Λ aY)) M) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ f
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) f
  exact (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
    ).isIso_dualComparison_of_isIso_projection
    (leftDerivedUpperStar_map_braiding_hom_δ (ModuleCat.{u + 1} Λ) f)
    ((rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f))
    γ.symm M fun T ↦
      inferInstanceAs (IsIso (((rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} Λ) f).app M).app T))

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--4`: for a proper `f : X ⟶ Y`, the
composite of `Rf_* δ_K : Rf_* K ⟶ Rf_* 𝔻_X 𝔻_X K` and the exchange
`c_{𝔻_X K} : Rf_* 𝔻_X (𝔻_X K) ≅ 𝔻_Y Rf_* (𝔻_X K)` equals the composite of
`δ_{Rf_* K} : Rf_* K ⟶ 𝔻_Y 𝔻_Y Rf_* K` and `𝔻_Y` applied to the exchange
`c_K : Rf_* 𝔻_X K ≅ 𝔻_Y Rf_* K`, that is, the square
```
            Rf_* δ_K
  Rf_* K ─────────────▶ Rf_* 𝔻_X 𝔻_X K
     │                        │
     │ δ_{Rf_* K}             │ c_{𝔻_X K}
     ▼                        ▼
  𝔻_Y 𝔻_Y Rf_* K ──────▶ 𝔻_Y Rf_* 𝔻_X K
             𝔻_Y c_K
```
commutes.

Here `𝔻 = RHom(-, ω)` is written `(ihom -).obj ω`, `δ` is
`CategoryTheory.MonoidalClosed.toIhomIhom` (`AlgebraicGeometry.Etale.verdierDualDoubleDual_app`),
`𝔻_Y` on morphisms is `CategoryTheory.MonoidalClosed.pre`, and the exchange `c` is the canonical
morphism `CategoryTheory.MonoidalClosed.dualComparison` of `Rf_*` and the trace, an isomorphism
(`AlgebraicGeometry.Etale.isIso_dualComparison_rightDerivedLowerStar`). It goes in the direction
`Rf_* 𝔻_X ⟶ 𝔻_Y Rf_*`, the inverse direction of the blueprint's `(10.3)` (with `Rf_! = Rf_*`). -/
theorem rightDerivedLowerStar_map_toIhomIhom_comp_dualComparison
    (γ : (R(f)^![Λ]).obj (dualizingComplex Λ aY) ≅ dualizingComplex Λ aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := rightDerivedLowerStarLaxBraided Λ f
    (R((f)_*[ModuleCat.{u + 1} Λ])).map (toIhomIhom (dualizingComplex Λ aX) K) ≫
        dualComparison (R((f)_*[ModuleCat.{u + 1} Λ]))
          ((R((f)_*[ModuleCat.{u + 1} Λ])).map γ.symm.hom ≫
            ((rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
              (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f)).counit.app
              (dualizingComplex Λ aY)) ((ihom K).obj (dualizingComplex Λ aX)) =
      toIhomIhom (dualizingComplex Λ aY) ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (pre (dualComparison (R((f)_*[ModuleCat.{u + 1} Λ]))
          ((R((f)_*[ModuleCat.{u + 1} Λ])).map γ.symm.hom ≫
            ((rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
              (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f)).counit.app
              (dualizingComplex Λ aY)) K)).app (dualizingComplex Λ aY) :=
  letI := rightDerivedLowerStarLaxBraided Λ f
  map_toIhomIhom_comp_dualComparison _ _ K

end Etale

end AlgebraicGeometry
