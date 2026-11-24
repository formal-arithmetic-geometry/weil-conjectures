/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk

/-! # Projectivity of the stalk of a finite free module sheaf

## References

* Stacks Project, Cohomology of Sheaves, Tag 08C4; Modules, Tag 01AG.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of a finite free module sheaf on the localized site is projective.
(Stacks, Tags 08C4 and 01AG) -/
theorem openModuleStalk_free_projective
    (Y : Scheme.{u}) (U : Y.Opens) (y : U.toScheme) (m : ℕ) :
    Projective ((openModuleStalkFunctor Y U y).obj
      (SheafOfModules.free
        (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin m)))) := by
  let S := openModuleStalkFunctor Y U y
  let R := ModuleCat.restrictScalars (U.ι.stalkMap y).hom
  let T := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y ⋙ R
  obtain ⟨e, _, _⟩ := Scheme.ideal_module_product_stalk
    (𝟙 (SheafOfModules.unit U.toScheme.ringCatSheaf))
    (SheafOfModules.unit U.toScheme.ringCatSheaf) y
  let er := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
  let eu : S.obj (SheafOfModules.unit ((moduleRings Y.toRingedSpace).over U)) ≅
      ModuleCat.of (Y.presheaf.stalk (U.ι y)) (Y.presheaf.stalk (U.ι y)) :=
    T.mapIso (Scheme.Modules.overEquivFunctorObjUnitIso U).symm ≪≫
      R.mapIso e ≪≫ ModuleCat.restrictScalarsIsoOfEquiv er
  have : Projective (S.obj
      (SheafOfModules.unit ((moduleRings Y.toRingedSpace).over U))) :=
    Projective.of_iso eu.symm inferInstance
  let c := PreservesCoproduct.iso S (fun _ : ULift.{u} (Fin m) ↦
    SheafOfModules.unit ((moduleRings Y.toRingedSpace).over U))
  exact Projective.of_iso c.symm inferInstance

end
end AlgebraicGeometry
