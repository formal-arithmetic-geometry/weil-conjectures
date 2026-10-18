/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The base change map for a pushforward tensored with a finite pushforward

Let `h ≫ f' = e ≫ g` be a commutative square, `π : X'₁ ⟶ X'` a finite morphism and
`Y₁ = X'₁ ×_{X'} Y`. For `M ∈ D(X'₁)`, the base change map
`Rπ_* M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Rπ_* M ⊗ᴸ Le^* F)` is identified with `Rπ_*` of the base
change map of the square `h₁ ≫ (π ≫ f') = (ρ ≫ e) ≫ g` at `M`, using the projection formula for
the finite morphisms `π`, `ρ`, finite base change and `Rh_* Rρ_* = Rπ_* Rh₁_*`. In particular
it is an isomorphism as soon as the latter is
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_rightDerivedLowerStar_of_isFinite`).

This is the computation with the finite morphisms `π_i` in the proof of blueprint
`lem-kun-0f1j` (via `lemma-weil-pbc-finite-exchange`, `lem-kun-0f0g`, `lem-kun-leray-finite`
and `lem-kun-proj-formula-natural`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X' S' T Y X'₁ Y₁ : Scheme.{u}}

/-- The base change map at a finite pushforward `Rπ_* M` is an isomorphism if the base change map
of the pulled back square at `M` is. -/
theorem isIso_tensorBaseChangeMap_rightDerivedLowerStar_of_isFinite [Finite Λ]
    (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (π : X'₁ ⟶ X') [IsFinite π] (h₁ : Y₁ ⟶ X'₁) (ρ : Y₁ ⟶ Y) (_sq : IsPullback h₁ ρ π h)
    (w₁ : h₁ ≫ π ≫ f' = (ρ ≫ e) ≫ g)
    (M : DerivedCategory (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_H : IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h₁ (ρ ≫ e) (π ≫ f') g w₁ M F)) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
      (R((π)_*[ModuleCat.{u + 1} Λ]).obj M) F) :=
  sorry

end Etale

end AlgebraicGeometry
