module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.Topology.PresheafModuleStalkFunctor

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- The stalk of sheaf tensor multiplication has image equal to the ideal generated
by the stalk image of the ideal map. This is the pure-tensor calculation in the
proof of `ideal_multiplication_stalk_range`; it follows from the stalk tensor
comparison and the germ formula for `e`.
Source: Stacks Project, Modules, Lemmas 01AG and 01CB.
(blueprint: lem-weil-pbc-ideal-multiplication-stalk-range-tensor).
-/
theorem stalk_tensor_multiplication_range {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    LinearMap.range (S.map (ι ▷ F ≫ (λ_ F).hom)).hom =
      (LinearMap.range (S.map ι ≫ e.hom).hom : Ideal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) := by
  sorry

end
end AlgebraicGeometry.Scheme
