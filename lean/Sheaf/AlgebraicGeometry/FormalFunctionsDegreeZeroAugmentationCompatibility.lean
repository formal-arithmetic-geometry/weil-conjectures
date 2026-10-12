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
/-- The fibre-system identification intertwines theta with section pullback on
classes obtained from the fixed degree-zero direct-image augmentation.
Source: Stacks Project, Tags 01E4 and 01FB (degree zero), and Tag 02OD for the
formal-fibre notation. No formal-functions completion theorem is used.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-augmentation-compatibility).

Proof: At each n compose the inverse of the global-sections degree-zero
augmentation with global sections of tensorPullbackObjUnitToUnit. Both maps are
isomorphisms; restrict their scalars to the completed local ring. The augmentation
square for moduleCohomologyFMap and the tensor-unit equation show that these
component isomorphisms commute with the transition morphisms. They therefore
form an inverse-system isomorphism b. Fix n, theta, V, hy, hV and t. In the
restricted injective resolution take xi to be the global-sections augmentation
of t. The resolutionSectionClass construction followed by isoRightDerivedObj.inv
sends xi to the direct-image augmentation of t on V: both are the class of the
resolution's zeroth augmentation of t. Naturality of germs identifies its germ
with the displayed stalk-map image. Apply IsFormalFunctionsTheta to xi. By the
augmentation square, the right-hand cohomology map corresponds under b to
section pullback of t. The containment hV says the inverse-image open is top;
hence the left restriction is the identity after transport along that equality.
Cancelling it gives the formula. This argument also covers empty fibres (all
sections and cohomology are zero) and t = 0, and requires no properness. -/
theorem formalFunctions_degreeZero_augmentation_compatibility {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) :
    ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y,
        ∀ (n : ℕ)
          (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
            Y.presheaf.stalk y]
            formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
          ∀ (V : Y.Opens) (hy : y ∈ V)
            (hV : (⊤ : (formalFibre f y n).Opens) ≤
              (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
            (b.hom.app (op n)) (θ (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
              ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app
                (SheafOfModules.unit X.ringCatSheaf))).hom (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj
                (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
              (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t := by sorry
end AlgebraicGeometry
