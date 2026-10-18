/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.Sites.Point.Flat

/-!
# Direct images of flat sheaves along finite morphisms are flat

For a finite morphism `π : X ⟶ Y` and a flat sheaf `F` of `Λ`-modules on `X_ét`, the direct
image `π_* F` is flat (`AlgebraicGeometry.Etale.flat_lowerStar_obj_of_isFinite`): its stalk at a
geometric point of `Y` is the finite product of the stalks of `F` at the geometric points over it
(`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`), and flatness is checked on stalks
(`CategoryTheory.GrothendieckTopology.flat_of_forall_flat_sheafFiber_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The direct image of a flat sheaf along a finite morphism is flat. This is used in the proof
of blueprint `lem-kun-0f1j` for the sheaves `π_* Λ`. -/
theorem flat_lowerStar_obj_of_isFinite {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((π)_*[ModuleCat.{u + 1} Λ].obj F) :=
  sorry

/-- The direct image of the unit along a finite morphism is flat. -/
theorem flat_lowerStar_obj_tensorUnit_of_isFinite {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] :
    ObjectProperty.flat ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _)) :=
  sorry

end Etale

end AlgebraicGeometry
