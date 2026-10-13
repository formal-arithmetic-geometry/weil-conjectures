/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps

/-! # Natural tensor comparison for derived open restriction

Source: Stacks Project, Tag 06YH (derived tensor construction) and Tag 08EU (locality).
(blueprint: lem-pc-derived-tensor-open-restriction-natural).
-/

@[expose] public section

universe u w wO
open CategoryTheory MonoidalCategory
set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace AlgebraicGeometry

/-- Exact open restriction commutes naturally with the derived tensor bifunctor.
Source: Stacks Project, Tag 06YH (derived tensor construction) and Tag 08EU, locality.
Proof: use the full category of K-flat models for both tensor inputs. Every
complex admits a K-flat resolution, and exact open restriction preserves
K-flatness. The natural sheaf tensor restriction comparison,
and commutation of restriction with the coproducts defining totalization, identify
restriction of the total tensor with the total tensor of restrictions. The K-flat
comparison identifies these models with the chosen derived tensors. Naturality in
complex maps and invariance under quasi-isomorphisms descend the comparison and its
inverse through the product derived localization. K-flat resolutions of common
refinements of quasi-isomorphism roofs show that the result is independent of the
models and natural in arbitrary derived morphisms. Transport by the derived-category
comparison equivalences accommodates independent universes. The comparison and its
inverse satisfy the two identity equations already on total tensor models, hence
also after localization. This construction applies to the empty open as well.
(blueprint: lem-pc-derived-tensor-open-restriction-natural). -/
theorem derivedTensor_openRestriction_natIso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    Nonempty (tensor (schemeDerivedCategory X) ⋙ R ≅
      R.prod R ⋙ tensor (schemeDerivedCategory U.toScheme)) := by sorry

end AlgebraicGeometry
