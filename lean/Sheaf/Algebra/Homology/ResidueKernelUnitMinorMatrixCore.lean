module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat
/--
(blueprint: new-residue-kernel-unit-minor-matrix-core)
Matrix unit-minor normalization over a local ring, assuming the localized modules are free.
Source: Stacks Project, Tags 00O0 and 00NX, matrix unit-minor argument.
The proof chooses a maximal nonzero residue minor and performs elementary row
and column operations. -/
theorem residue_kernel_unit_minor_matrix_core
    (R : Type v) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [IsLocalRing A] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (hX : Module.Free A
      ((ModuleCat.extendScalars (algebraMap R A)).obj X))
    (hY : Module.Free A ((ModuleCat.extendScalars (algebraMap R A)).obj Y))
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars
      ((IsLocalRing.residue A).comp (algebraMap R A))).map f).hom
      ≃ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A)) :
    ∃ (U C : ModuleCat.{v} A) (g : A →ₗ[A] C), Module.Free A C ∧
      ∃ (eX : ((ModuleCat.extendScalars (algebraMap R A)).obj X)
          ≃ₗ[A] (U × A)) (eY : ((ModuleCat.extendScalars (algebraMap R A)).obj Y)
          ≃ₗ[A] (U × C)),
        ∀ x, eY (((ModuleCat.extendScalars (algebraMap R A)).map f).hom x) =
          ((eX x).1, g (eX x).2) := by sorry
end ModuleCat
