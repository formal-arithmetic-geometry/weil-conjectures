/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The counit identity at the coefficient unit

This is the abstract mate calculation used at the unit object in the finite
coefficient theta-factor argument.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory

/-- A counit mate at the unit, followed by a morphism out of the changed unit,
is the counit at the target followed by the changed mate.  This is the
`v = ε_{B,1} F_B w` identity from the coefficient-reduction proof.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 4
(blueprint: lem-pur-finite-reduction-theta-factor-b-counit).

Proof: rewrite the defining mate equation for `b`, then use naturality of the
second adjunction counit at `u`.  Functoriality changes the resulting composite
to the map of `w = b ≫ G_B(u)`.  The argument is purely categorical and hence
applies to the intrinsic finite-coefficient adjunctions after specialization.
-/
theorem finiteReduction_thetaFactor_b_counit_identity
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (FA : C ⥤ D) (GA : D ⥤ C) (FB : E ⥤ F) (GB : F ⥤ E)
    (QX : C ⥤ E) (QY : D ⥤ F)
    (q : FA ⋙ QY ≅ QX ⋙ FB)
    (adjA : FA ⊣ GA) (adjB : FB ⊣ GB)
    {I : D} {J : F}
    (u : QY.obj I ⟶ J)
    (b : QX.obj (GA.obj I) ⟶ GB.obj (QY.obj I))
    (hb : FB.map b ≫ adjB.counit.app (QY.obj I) =
      q.inv.app (GA.obj I) ≫ QY.map (adjA.counit.app I)) :
    q.inv.app (GA.obj I) ≫ QY.map (adjA.counit.app I) ≫ u =
      FB.map (b ≫ GB.map u) ≫ adjB.counit.app J := by
  calc
    _ = (FB.map b ≫ adjB.counit.app (QY.obj I)) ≫ u := by
      simpa only [Functor.comp_obj, Category.assoc] using
        congrArg (fun z ↦ z ≫ u) hb.symm
    _ = FB.map b ≫ (FB.map (GB.map u) ≫ adjB.counit.app J) := by
      rw [Category.assoc]
      exact congrArg (fun z ↦ FB.map b ≫ z) (adjB.counit.naturality u).symm
    _ = _ := by rw [FB.map_comp, Category.assoc]
