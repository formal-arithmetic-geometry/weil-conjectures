/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Presheaf of locally constant maps

The presheaf of locally constant maps into a fixed set.

## References

* [Stacks Project, Tag 006W](https://stacks.math.columbia.edu/tag/006W)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- The presheaf assigning to each open the locally constant maps into `R`. -/
def locallyConstantMapsPresheaf (X : TopCat.{u}) (R : Type v) :
    X.Presheaf (Type (max u v)) where
  obj := fun V ↦ LocallyConstant {x : X // x ∈ unop V} R
  map := fun {U V} f ↦ TypeCat.ofHom (LocallyConstant.comap
    ⟨fun x : {x : X // x ∈ unop V} ↦ ⟨x.1, f.unop.le x.2⟩,
      continuous_subtype_val.subtype_mk _⟩)
  map_id := by intros; rfl
  map_comp := by intros; rfl

end TopCat
