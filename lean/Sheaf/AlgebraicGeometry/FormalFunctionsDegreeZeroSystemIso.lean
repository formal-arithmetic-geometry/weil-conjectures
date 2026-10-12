module
public import Sheaf.AlgebraicGeometry.FormalFibreCohomology
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.TensorPullback
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Degree-zero fibre cohomology is naturally the section system for the unit
module.
Proof: Identify degree-zero module cohomology with sections via augmentation,
use tensor pullback of the unit module, and check transition naturality.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-system-iso) -/
theorem formalFunctions_degreeZero_systemIso {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y, True := by sorry
end AlgebraicGeometry
