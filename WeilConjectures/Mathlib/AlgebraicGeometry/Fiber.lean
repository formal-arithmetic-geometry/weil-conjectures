/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The scheme-theoretic fibre: residue fields and open neighbourhoods of the base point

If `f : X ⟶ Y` is surjective on stalks — for instance a preimmersion, and in particular the
inclusion `f.fiberι y` of a scheme-theoretic fibre — then the induced map `κ(f x) ⟶ κ(x)` on
residue fields is an isomorphism.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.surjective_residueFieldMap`
- `AlgebraicGeometry.isIso_residueFieldMap`
- `AlgebraicGeometry.Scheme.Hom.preimage_fiberι_eq_top`: the fibre over `y` lies over every open
  neighbourhood of `y`.

This is stated in the mirror of `Mathlib/AlgebraicGeometry/Fiber.lean` because that is the first
file of Mathlib that imports both `Mathlib/AlgebraicGeometry/ResidueField.lean`, where
`Scheme.Hom.residueFieldMap` lives, and
`Mathlib/AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X)

/-- A morphism that is surjective on stalks is surjective on residue fields. -/
lemma Scheme.Hom.surjective_residueFieldMap : Function.Surjective (f.residueFieldMap x) := by
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨IsLocalRing.residue _ c, rfl⟩

/-- A morphism that is surjective on stalks induces isomorphisms on residue fields: the map
`κ(f x) ⟶ κ(x)` is surjective by `Scheme.Hom.surjective_residueFieldMap` and injective because
it is a ring homomorphism between fields. -/
instance isIso_residueFieldMap : IsIso (f.residueFieldMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap x).hom.injective, f.surjective_residueFieldMap x⟩

section Fiber

variable {X Y : Scheme.{u}}

/-- Every point of the fibre of `f` over `y` lies over `y`. -/
lemma Scheme.Hom.apply_fiberι (f : X ⟶ Y) (y : Y) (x : f.fiber y) : f (f.fiberι y x) = y := by
  have hx : f.fiberι y x ∈ f ⁻¹' {y} := f.range_fiberι y ▸ Set.mem_range_self x
  simpa using hx

/-- **The fibre of `f` over `y` lies over every open neighbourhood of `y`.** -/
lemma Scheme.Hom.preimage_fiberι_eq_top (f : X ⟶ Y) {y : Y} {U : Y.Opens} (hU : y ∈ U) :
    f.fiberι y ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
  ext x
  simpa [f.apply_fiberι y x] using hU

end Fiber

end AlgebraicGeometry
