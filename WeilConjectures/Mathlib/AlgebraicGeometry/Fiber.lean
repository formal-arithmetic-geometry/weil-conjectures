/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The scheme-theoretic fibre: residue fields and open neighbourhoods of the base point

If `f : X ⟶ Y` is surjective on stalks — for instance a preimmersion, and in particular the
inclusion `f.fiberι y` of a scheme-theoretic fibre — then the induced map `κ(f x) ⟶ κ(x)` on
residue fields is an isomorphism.

Every point of the scheme-theoretic fibre `X_y` lies over `y`, so `X_y` lies over every open
neighbourhood of `y` in `Y`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.surjective_residueFieldMap`
- `AlgebraicGeometry.isIso_residueFieldMap`
- `AlgebraicGeometry.Scheme.Hom.apply_fiberι`: a point of the fibre over `y` lies over `y`.
- `AlgebraicGeometry.Scheme.Hom.preimage_fiberι_eq_top`: the fibre over `y` lies over every open
  neighbourhood of `y`.
- `AlgebraicGeometry.Scheme.Hom.fiberLift`: the resulting morphism from the fibre over `y` to the
  open subscheme `f ⁻¹ᵁ V`, for an open neighbourhood `V` of `y`.

The residue field statements are in the mirror of `Mathlib/AlgebraicGeometry/Fiber.lean` because
that is the first file of Mathlib that imports both
`Mathlib/AlgebraicGeometry/ResidueField.lean`, where `Scheme.Hom.residueFieldMap` lives, and
`Mathlib/AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

section ResidueField

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

end ResidueField

section Fiber

variable {X Y : Scheme.{u}}

/-- Every point of the fibre of `f` over `y` lies over `y`. -/
@[simp]
lemma Scheme.Hom.apply_fiberι (f : X ⟶ Y) (y : Y) (x : f.fiber y) : f (f.fiberι y x) = y := by
  simpa using congrArg (fun g : f.fiber y ⟶ Y ↦ g.base x) (f.fiber_fac y)

/-- **The fibre of `f` over `y` lies over every open neighbourhood of `y`.** -/
lemma Scheme.Hom.preimage_fiberι_eq_top (f : X ⟶ Y) {y : Y} {U : Y.Opens} (hU : y ∈ U) :
    f.fiberι y ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
  ext x
  simpa using hU

variable (f : X ⟶ Y) {V : Y.Opens} {y : Y} (hy : y ∈ V)

/-- **The fibre of `f` over a point of `V` as a scheme over the open subscheme `f ⁻¹ᵁ V`.** Every
point of the fibre over `y` lies over `y`, hence over `V`, so the inclusion of the fibre factors
through the open immersion `f ⁻¹ᵁ V ⟶ X`. -/
noncomputable def Scheme.Hom.fiberLift : f.fiber y ⟶ (f ⁻¹ᵁ V).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (f.fiberι y) (by
    rw [Scheme.Opens.range_ι, f.range_fiberι]
    rintro x (hx : f.base x = y)
    change f.base x ∈ V
    rw [hx]
    exact hy)

@[reassoc (attr := simp)]
lemma Scheme.Hom.fiberLift_ι : f.fiberLift hy ≫ (f ⁻¹ᵁ V).ι = f.fiberι y :=
  IsOpenImmersion.lift_fac _ _ _

@[simp]
lemma Scheme.Hom.fiberLift_apply (x : f.fiber y) :
    (f ⁻¹ᵁ V).ι (f.fiberLift hy x) = f.fiberι y x := by
  rw [← f.fiberLift_ι hy]
  rfl

instance : IsPreimmersion (f.fiberLift hy) :=
  have : IsPreimmersion (f.fiberLift hy ≫ (f ⁻¹ᵁ V).ι) := by
    rw [f.fiberLift_ι hy]; infer_instance
  IsPreimmersion.of_comp (f.fiberLift hy) (f ⁻¹ᵁ V).ι

end Fiber

end AlgebraicGeometry
