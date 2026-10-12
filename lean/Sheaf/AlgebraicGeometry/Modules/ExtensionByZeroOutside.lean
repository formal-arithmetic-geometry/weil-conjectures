module
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.Topology.PresheafModuleStalkFunctor
import Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import Mathlib.Algebra.Category.Grp.Zero
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
theorem module_extensionByZero_outside_stalk (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∀ (F : SheafOfModules.{u} (R.over U)) (x : X), x ∉ U →
      IsZero (TopCat.Presheaf.stalk (L.obj F).val.presheaf x) := by
  dsimp
  intro F x hx
  have h := ModuleExtensionByZeroStalkOutside X.toRingedSpace U F x hx
  apply (AddCommGrpCat.isZero_iff_subsingleton).mpr
  have hs := (ModuleCat.isZero_iff_subsingleton).mp h
  exact hs
end AlgebraicGeometry.Scheme.Modules
