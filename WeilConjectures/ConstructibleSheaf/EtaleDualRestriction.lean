/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-! # Étale restriction of coefficient duals

Pullback along an étale map `U ⟶ X` commutes with the coefficient dual `Hom(F, Λ)` of an
arbitrary sheaf of `Λ`-modules on the small étale site.

## Main results

- `AlgebraicGeometry.Scheme.nonempty_etaleDualRestrictionIso`
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- Étale pullback commutes with the coefficient dual, without finiteness assumptions:
`U^*(Hom(F, Λ)) ≅ Hom(U^*F, Λ)` for every sheaf of `Λ`-modules `F`. -/
theorem nonempty_etaleDualRestrictionIso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (U : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj
      ((ihom F).obj (𝟙_ _)) ≅
      (ihom ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F)).obj (𝟙_ _)) := by
  have := Etale.isIso_ihomComparison_upperStar (ModuleCat.{u + 1} Λ) U.hom F
  let e := asIso ((Functor.LaxMonoidal.ihomComparison
    (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom) F).app (𝟙_ _))
  exact ⟨e ≪≫ (ihom ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F)).mapIso
    (Functor.Monoidal.εIso (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom)).symm⟩

end AlgebraicGeometry.Scheme
