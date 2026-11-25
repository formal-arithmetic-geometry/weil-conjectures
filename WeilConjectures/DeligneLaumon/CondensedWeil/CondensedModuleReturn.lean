/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # The specified module return before geometric evaluation

This file defines the semilinear module return built from the pullback compositors and a
return equation, and its evaluation after a point insertion.

## Implementation details

The module return is kept separate from the later scalar evaluation: the local Frobenius
operator uses precisely these maps before scalar evaluation. No data is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil

/-- The semilinear module return from the specified compositors and return equation. -/
@[irreducible] def moduleReturnMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S X : Scheme.{u}} (a : X ⟶ X) (s : S ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (θ : (CondensedRing.upperStar Λ a).obj M ⟶ M) (z : S ⟶ X)
    (h : z ≫ a = s ≫ z) :
    (CondensedRing.upperStar Λ s).obj ((CondensedRing.upperStar Λ z).obj M) ⟶
      (CondensedRing.upperStar Λ z).obj M :=
  (CondensedRing.upperStarComp Λ s z).inv.app M ≫
    eqToHom (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) h.symm) ≫
      (CondensedRing.upperStarComp Λ z a).hom.app M ≫
        (CondensedRing.upperStar Λ z).map θ

/-- Apply a specified point insertion, then evaluate a semilinear return. -/
@[irreducible] def evaluateModuleReturn
    {C E : Type*} [Category C] [Category E] (F : C ⥤ E) (T : C ⥤ C)
    (ι : F ⟶ T ⋙ F) (M : C) (r : T.obj M ⟶ M) : End (F.obj M) :=
  .of (ι.app M ≫ F.map r)

end WeilConjectures.CondensedWeil
