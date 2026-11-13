/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.StalkTensorMultiplicationRange
import WeilConjectures.AlgebraicGeometry.StalkImageRange

/-! # Range of ideal multiplication on module stalks

## References

* Stacks Project, Tags 01AG and 01CB
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- The image of the stalk multiplication map is the ideal times the module.
(Stacks, Tags 01AG and 01CB) -/
theorem ideal_multiplication_stalk_range {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    LinearMap.range (S.map (image.ι (ι ▷ F ≫ (λ_ F).hom))).hom =
      (LinearMap.range (S.map ι ≫ e.hom).hom : Ideal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) := by
  dsimp
  let _ : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  rw [stalk_image_inclusion_range]
  exact stalk_tensor_multiplication_range ι F x e he

end
end AlgebraicGeometry.Scheme
