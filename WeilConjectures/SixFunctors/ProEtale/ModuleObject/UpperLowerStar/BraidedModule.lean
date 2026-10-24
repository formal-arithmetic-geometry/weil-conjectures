/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!

# The pullback of module objects is braided

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The pullback
`f^* = mapMod(f^*) ⋙ Ext_{α_f} : Mod_{Λ_Y} ⥤ Mod_{Λ_X}` of module objects is compatible with the
symmetries of the relative tensor products (`ProEtale.CondensedRing.laxBraided_upperStar`): both
factors are (`Functor.laxBraided_mapMod`, `Mod.laxBraided_extendScalars`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module objects over `Λ` is braided for the
symmetric relative tensor products, as the composite of two braided functors. -/
noncomputable instance laxBraided_upperStar : (f)^*⟦Λ⟧.LaxBraided :=
  inferInstanceAs ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y) ⋙
    Mod.extendScalars (condensedPullbackHom Λ f)).LaxBraided

end AlgebraicGeometry.ProEtale.CondensedRing
