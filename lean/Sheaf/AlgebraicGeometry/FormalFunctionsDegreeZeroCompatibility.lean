module
public import Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroStalkIso
import Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- The degree-zero identifications carry every canonical theta to pullback of
sections, by augmentation and restriction compatibility.
Proof: Evaluate the defining theta compatibility on the degree-zero augmentation
class of a germ; under the two identifications this is pullback of the section.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-compatibility) -/
theorem formalFunctions_degreeZero_compatibility {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y)
    (a : ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) ≃ₗ[
          Y.presheaf.stalk y]
        formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0)
    (b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y) :
    ∀ (n : ℕ)
      (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
        Y.presheaf.stalk y]
        formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
      IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
      ∀ (V : Y.Opens) (hy : y ∈ V)
        (hV : (⊤ : (formalFibre f y n).Opens) ≤
          (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
        (b.hom.app (op n)) (θ (a (TopCat.Presheaf.germ
          ((Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
          (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t := by sorry
end AlgebraicGeometry
