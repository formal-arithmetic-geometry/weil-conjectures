/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.AffineHomComparisonLeft
import WeilConjectures.AlgebraicGeometry.AffineHomComparisonRight
import WeilConjectures.AlgebraicGeometry.AffineHomComparisonRankOne

/-! # Natural affine Hom comparison maps

## References

* Stacks Project, Tags 01HV and 0BQZ
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The forward affine Hom comparison exists for arbitrary modules, is natural
in both arguments, and is invertible when the source is the rank-one module
(Stacks, Tags 01HV, 0BQZ). -/
theorem exists_affine_hom_comparison_maps {Y : Scheme.{u}} (U : Y.affineOpens) :
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    ∃ c : ∀ (M N : ModuleCat.{u} A),
        T.obj (ModuleCat.of A (M ⟶ N)) ⟶
          SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
            (T.obj M) (T.obj N),
      (∀ (M M' N : ModuleCat.{u} A) (f : M' ⟶ M),
        c M N ≫ SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
          (T.map f) (𝟙 (T.obj N)) =
        T.map (ModuleCat.ofHom (Linear.leftComp A N f)) ≫ c M' N) ∧
      (∀ (M N N' : ModuleCat.{u} A) (g : N ⟶ N'),
        c M N ≫ SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
          (𝟙 (T.obj M)) (T.map g) =
        T.map (ModuleCat.ofHom (Linear.rightComp A M g)) ≫ c M N') ∧
      (∀ N : ModuleCat.{u} A, IsIso (c (ModuleCat.of A A) N)) := by
  rw [← affineHomComparisonFunctor_eq U]
  dsimp only
  exact ⟨affineHomComparison U, affineHomComparison_chart_left U,
    affineHomComparison_chart_right U, affineHomComparison_chart_rankone U⟩

end AlgebraicGeometry
