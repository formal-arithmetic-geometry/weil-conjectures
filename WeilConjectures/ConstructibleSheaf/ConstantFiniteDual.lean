/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.ConstructibleSheaf.ConstantModuleDual

/-! # Dual of a constant finite module sheaf
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

/-- Constant sheafification commutes with the coefficient dual of a finite module. -/
theorem nonempty_constant_finite_dual_iso (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    Nonempty ((ihom ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj
      (𝟙_ _) ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (M →ₗ[Λ] Λ))) := by
  exact nonempty_constantModuleDualIso X M

end AlgebraicGeometry.Scheme
