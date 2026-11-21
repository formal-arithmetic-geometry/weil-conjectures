/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Generator.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Flatness of the sheafified free presheaf

## Main statement

The sheaf associated to the free presheaf on a representable, with a flat
coefficient object, is flat.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A]

/--
The sheafification of the free presheaf on a representable with flat
coefficient object is flat, expressed as preservation of finite limits by
left tensoring. This is Lemma 03EV of the Stacks Project, generalized to
Grothendieck abelian symmetric monoidal closed coefficient categories.
Source: Stacks Project, Modules on Sites, Lemmas 03EV, 03ES, 03ET and 0GMW. -/
lemma free_sheaf_flat (P : A) (hP : PreservesFiniteLimits (tensorLeft P))
    (X : C) :
    PreservesFiniteLimits (tensorLeft (Sheaf.freeYoneda J X P)) := by
  -- Retain the additivity hypothesis in the existing theorem interface.
  have _hadd : MonoidalPreadditive A := inferInstance
  apply (ObjectProperty.flat_iff_preservesFiniteLimits _).1
  change ObjectProperty.flat ((presheafToSheaf J A).obj (Presheaf.freeYoneda X P))
  apply flat_presheafToSheaf_obj A J
  intro V
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{_, _, u + 1} A
    (ULift.{u + 1} (V.unop ⟶ X))
  exact ObjectProperty.prop_of_iso _
    (Sigma.whiskerEquiv (f := fun _ : ULift.{u + 1} (V.unop ⟶ X) ↦ P) Equiv.ulift
      fun _ ↦ Iso.refl P)
    (ObjectProperty.flat_coproduct _ fun _ ↦
      (ObjectProperty.flat_iff_preservesFiniteLimits P).2 hP)

end CategoryTheory.GrothendieckTopology
