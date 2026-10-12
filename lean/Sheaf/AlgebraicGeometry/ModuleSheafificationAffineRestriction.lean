/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Sheafification of module presheaves identified on affine opens

Source: Stacks Project, Tags 009U and 0089, the module basis equivalence and the
universal property of module sheafification
(blueprint: lem-sc-module-sheafification-affine-restriction).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

/-- A natural identification with a module sheaf on all affine opens extends after
sheafification, naturally in an arbitrary parameter category.
Source: Stacks Project, Tags 009U and 0089
(blueprint: lem-sc-module-sheafification-affine-restriction).

Proof: Affine opens form a basis. For each parameter, extend the given affine-open
maps into the target sheaf to all opens: cover each open by affine opens, apply the
maps to the restrictions of a section, and glue in the target. On overlaps, use
an affine refinement and restriction compatibility; uniqueness proves independence
of the cover. Addition and scalar multiplication hold locally, hence globally.
The resulting module-presheaf map factors uniquely through sheafification. On each
stalk, affine neighbourhoods are cofinal, so the given affine isomorphisms induce
an isomorphism on the stalks. Sheafification preserves these stalks. Consequently
the factored sheaf morphism is an isomorphism. For a parameter morphism, the two
composites agree on every affine open before factoring; uniqueness of extension
and of factorization proves naturality. No intersection of affine opens needs to
be affine: it is covered by affine opens. Empty opens use the empty sheaf cover. -/
theorem module_sheafification_iso_of_affine_restriction
    (Y : Scheme.{u}) {C : Type v} [Category.{w} C]
    (P : C ⥤ PresheafOfModules.{u} (moduleRings Y.toRingedSpace).obj)
    (Q : C ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (e : P ⋙ PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
        (moduleRings Y.toRingedSpace).obj ≅
      Q ⋙ SheafOfModules.forget (moduleRings Y.toRingedSpace) ⋙
        PresheafOfModules.pushforward₀
          (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
          (moduleRings Y.toRingedSpace).obj) :
    Nonempty (P ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings Y.toRingedSpace).obj) ≅ Q) := by
  sorry

end AlgebraicGeometry
