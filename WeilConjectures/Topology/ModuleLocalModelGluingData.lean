/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

/-!
# Gluing data for prescribed local module families

Source: Stacks Project, Modules, Tag 01BC, proof of
`lemma-set-isomorphism-classes-finite-type-modules`.
(blueprint: def-weil-pbc-module-local-model-gluing-data)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- All covers without repetitions, local-model labels, and module transition isomorphisms.
The cocycle is equality on every open in a triple overlap, including repeated indices.
The localized site `Over U` retains exactly the sections on opens contained in `U`.

Source: Stacks Project, Modules, Tag 01BC, the set of coverings and gluing data in the proof.
(blueprint: def-weil-pbc-module-local-model-gluing-data) -/
structure ModuleLocalModelGluingData (X : RingedSpace.{u}) (I : Opens X → Type u)
    (B : ∀ U : Opens X, I U → ringedSiteModules.{u} ((moduleRings X).over U)) : Type u where
  /-- A subset of all opens, so that members are not repeated. -/
  cover : Set (Opens X)
  /-- The chosen opens cover the whole space. -/
  isCover : ⨆ U : cover, U.val = ⊤
  /-- The prescribed local model chosen on each cover member. -/
  label : ∀ U : cover, I U.val
  /-- The overlap identifications, also for equal cover members. -/
  transition : ∀ U V : cover,
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_left : U.val ⊓ V.val ⟶ U.val)).obj (B U.val (label U)) ≅
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_right : U.val ⊓ V.val ⟶ V.val)).obj (B V.val (label V))
  /-- Composition of transitions on every triple overlap. -/
  cocycle : ∀ (U V T : cover) (W : Opens X)
    (hU : W ≤ U.val) (hV : W ≤ V.val) (hT : W ≤ T.val),
    (transition U T).hom.val.app (op (Over.mk (homOfLE (le_inf hU hT)))) =
      (transition U V).hom.val.app (op (Over.mk (homOfLE (le_inf hU hV)))) ≫
        (transition V T).hom.val.app (op (Over.mk (homOfLE (le_inf hV hT))))

end AlgebraicGeometry
