module
public import Sheaf.AlgebraicGeometry.FormalFibreCohomology
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import Sheaf.Paper.HigherDirectImagePresheaf
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Degree-zero stalk comparison, obtained from the augmentation of the zeroth
right-derived direct image.
Proof: Apply the degree-zero augmentation comparison and take the stalk;
this gives the displayed equivalence.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-stalk-iso) -/
theorem formalFunctions_degreeZero_stalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    ∃ a : (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) ≃ₗ[
          Y.presheaf.stalk y]
        formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0), True := by sorry
end AlgebraicGeometry
