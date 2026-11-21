/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-! # Internal Hom and étale restriction

Étale pullback commutes with the internal Hom of sheaves of modules
(`nonempty_etale_upperStar_ihom_iso`).
-/

@[expose] public section

universe u




open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- Étale pullback commutes with internal Hom of module sheaves. -/
theorem nonempty_etale_upperStar_ihom_iso (f : Y ⟶ X) [Etale f]
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj ((ihom F).obj G) ≅
      (ihom ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G)) := by
  have := Etale.isIso_ihomComparison_upperStar
    (ModuleCat.{u + 1} Λ) f F
  exact ⟨asIso ((Functor.LaxMonoidal.ihomComparison
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f) F).app G)⟩

end AlgebraicGeometry.Scheme
