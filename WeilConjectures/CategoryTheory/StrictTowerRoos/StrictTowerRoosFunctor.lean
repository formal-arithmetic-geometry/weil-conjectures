/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The strict Roos functor on towers of cochain complexes

Source: current blueprint, det-pe-derived-nakayama-first-reduction, proof, Cones paragraph;
Stacks Project, Tag 08TC, definition-derived-limit, for the transition endomorphism.
(blueprint: def-sf-strict-roos-functor)

This constructs the fibre of one minus shift using actual categorical products and
the published signed mapping cocone. The construction requires countable products;
identification with a derived-category limit additionally requires the product comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory.Limits Opposite

namespace CategoryTheory.StrictTowerRoos

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

/-- The chosen product of a strict tower of complexes, with product maps on morphisms.
Source: det-pe-derived-nakayama-first-reduction, proof, Cones paragraph, termwise product;
Stacks Tag 08TC (blueprint: def-sf-strict-roos-functor). -/
noncomputable def productFunctor :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ where
  obj C := ∏ᶜ (fun n : ℕ ↦ C.obj (op n))
  map α := Limits.Pi.map (fun n : ℕ ↦ α.app (op n))
  map_id C := by
    simpa only [NatTrans.id_app] using
      (Limits.Pi.map_id (f := fun n : ℕ ↦ C.obj (op n)))
  map_comp α β := by
    simpa only [NatTrans.comp_app] using
      (Limits.Pi.map_comp_map (fun n : ℕ ↦ α.app (op n))
        (fun n : ℕ ↦ β.app (op n))).symm

/-- One minus the product shift, natural in strict tower maps.
Source: det-pe-derived-nakayama-first-reduction, proof, Cones paragraph; Stacks Tag 08TC
(blueprint: def-sf-strict-roos-functor).
The naturality field is the published transition-endomorphism naturality theorem,
applied to the naturality of the tower map on each adjacent transition. -/
noncomputable def boundary :
    productFunctor (A := A) ⟶ productFunctor (A := A) where
  app C := towerTransitionEndomorphism
    (fun n : ℕ ↦ C.map (homOfLE (Nat.le_succ n)).op)
  naturality C D α := by
    dsimp only [productFunctor]
    exact towerTransitionEndomorphism_natural_backward
      (fun n : ℕ ↦ C.map (homOfLE (Nat.le_succ n)).op)
      (fun n : ℕ ↦ D.map (homOfLE (Nat.le_succ n)).op)
      (fun n : ℕ ↦ α.app (op n))
      (fun n ↦ (α.naturality (homOfLE (Nat.le_succ n)).op).symm)

/-- The strict Roos functor `C ↦ Cone(1 - s_C)[-1]`. On a tower map `α`, the two
coordinates of the induced mapping-cocone map are both `Pi.map (fun n ↦ α.app (op n))`.
Source: det-pe-derived-nakayama-first-reduction, proof, Cones paragraph, the functorial
strict-tower fibre construction; Stacks Tag 08TC for `1 - s`.
(blueprint: def-sf-strict-roos-functor)

Construction: (1) form the product and its transition endomorphism; (2) use the
transition naturality theorem to obtain the diagonal commuting square; (3) apply
the signed mapping-cocone functor. Its published identity and composition laws
give the functor laws, retaining its actual cone coordinates and the product projections. -/
noncomputable def functor :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ :=
  SignedCoconeShift.coconeFunctor productFunctor productFunctor boundary

end CategoryTheory.StrictTowerRoos
