/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Iso
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Sets.Opens
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Topology.GlueSheavesOfModules

/-!
# Gluing a family of trivial module lines

This is the sheaf-theoretic gluing step used in the projective-bundle descent
argument.  The projective-bundle calculation supplies the transition
isomorphisms; this lemma packages the resulting glued module and its local
trivializations.
(blueprint: lem-sfb-projective-bundle-relatively-trivial-line-descent-gluing)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- A cocycle of transition isomorphisms between trivial module lines glues to
a module which is trivial on every member of the cover. -/
theorem glue_trivial_module_lines
    (X : RingedSpace.{u, u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (φij : ∀ i j : I,
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj
          (SheafOfModules.unit ((moduleRings X).over (U i))) ≅
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj
          (SheafOfModules.unit ((moduleRings X).over (U j))))
    (hcocycle : ∀ (i j k : I) (W : Opens X)
      (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
      (φij i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
        (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (φij j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) :
    ∃ (H : SheafOfModules (moduleRings X)),
      ∀ i : I, Nonempty (H.over (U i) ≅
        SheafOfModules.unit ((moduleRings X).over (U i))) := by
  obtain ⟨H, φi, hφi⟩ :=
    (glue_sheaves_of_modules X I U hcover).2.2
      (fun _ ↦ SheafOfModules.unit ((moduleRings X).over (U _))) φij hcocycle
  exact ⟨H, fun i ↦ ⟨φi i⟩⟩

end AlgebraicGeometry
