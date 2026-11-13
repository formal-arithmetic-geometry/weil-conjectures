/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-!
# A quasi-finite affine morphism embeds in a finite affine morphism

## References

* [Stacks Project, Tag 03GU](https://stacks.math.columbia.edu/tag/03GU)
* [Stacks Project, Tag 00QB](https://stacks.math.columbia.edu/tag/00QB)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-finite morphism between affine schemes factors as an open immersion into an
 affine scheme finite over the target. -/
theorem Scheme.Hom.exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (hf : f.IsQuasiFinite) :
    ∃ (Z : Scheme.{u}) (j : Y ⟶ Z) (π : Z ⟶ X),
      IsAffine Z ∧ IsOpenImmersion j ∧ IsFinite π ∧ f = j ≫ π := by
  let : LocallyOfFiniteType f := hf.1
  let : QuasiCompact f := hf.2.1
  have hlq : LocallyQuasiFinite f := by
    apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
    intro x
    apply isDiscrete_iff_discreteTopology.mpr
    apply discreteTopology_iff_isOpen_singleton.mpr
    rintro ⟨y, hy⟩
    change f y = x at hy
    subst x
    have hopen := hf.2.2 y
    rw [← (f.fiberHomeo (f y)).isOpen_image] at hopen
    simpa only [Set.image_singleton, Scheme.Hom.asFiber,
      Homeomorph.apply_symm_apply] using hopen
  let := hlq
  obtain ⟨Z, j, π, hj, _, hπ, hfac⟩ :=
    f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  let := hπ
  exact ⟨Z, j, π, isAffine_of_isAffineHom π, hj, hπ, hfac.symm⟩

end AlgebraicGeometry
