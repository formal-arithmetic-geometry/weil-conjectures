/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Images

/-! # Range of the stalk map of an image inclusion

## References

* Stacks Project, Modules, Lemma 01AG.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- At every point, the stalk map of the image inclusion of `f` has the same range as the
stalk map of `f`. -/
theorem stalk_image_inclusion_range {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    LinearMap.range (S.map (image.ι f)).hom = LinearMap.range (S.map f).hom := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have hr := ((RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.2.1 x).2.2
  have he : S.map (Abelian.imageIsoImage f).hom ≫ S.map (image.ι f) =
      S.map (Abelian.image.ι f) := by
    rw [← S.map_comp, Abelian.imageIsoImage_hom_comp_image_ι]
  have hs : Function.Surjective (S.map (Abelian.imageIsoImage f).hom).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  calc
    LinearMap.range (S.map (image.ι f)).hom =
        LinearMap.range (S.map (Abelian.image.ι f)).hom := by
      rw [← he, ModuleCat.hom_comp,
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)]
    _ = LinearMap.range (S.map f).hom := hr

end
end AlgebraicGeometry.Scheme
