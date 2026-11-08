/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.Additive

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Explicit increasing-tuple complexes of module sheaves

Source: Stacks Project, Tag 01FM, alternating face maps.
(blueprint: def-pc-s3-alternating-cech-sheaf-construction).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
noncomputable section

variable {X : Scheme.{u}}

/-- Intersection with a fixed open, as a functor on opens. Source: Stacks 01FM
(blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def cechCapFunctor (W : X.Opens) : X.Opens ⥤ X.Opens where
  obj V := V ⊓ W
  map h := homOfLE (inf_le_inf_right W (leOfHom h))

/-- Restriction of rings to intersections. Source: Stacks 01FM
(blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def cechCapRingMap (W : X.Opens) :
    X.ringCatSheaf.obj ⟶ (cechCapFunctor W).op ⋙ X.ringCatSheaf.obj where
  app V := X.ringCatSheaf.obj.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op
  naturality := by
    intro V Z h
    simp only [Functor.comp_map, ← Functor.map_comp]
    rfl

/-- The module presheaf with sections G(V ∩ W), scalars restricted from V.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def cechCapModule (G : X.Modules) (W : X.Opens) :
    PresheafOfModules.{u} X.ringCatSheaf.obj :=
  (PresheafOfModules.pushforward (cechCapRingMap W)).obj G.val

/-- The degree-p module presheaf, a finite product over increasing tuples.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def alternatingCechSheafPresheafTerms {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules)
    (p : ℕ) : PresheafOfModules.{u} X.ringCatSheaf.obj :=
  ∏ᶜ fun t : Fin (p + 1) ↪o Fin r ↦ cechCapModule G (alternatingCechIntersection U t)

end
end AlgebraicGeometry
