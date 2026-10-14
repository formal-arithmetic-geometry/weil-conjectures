module

public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import Sheaf.Algebra.Homology.BoundedFlatReplacement

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A bounded-above complex representative can be replaced by a termwise flat one.
Source: Stacks Project, Tag 077J.
(blueprint: new-pc-bounded-above-model-flat-replacement).
Apply the functorial bounded-above flat replacement to a good truncation of the
representative; its augmentation is a quasi-isomorphism, hence induces the
required isomorphism in the derived category. -/
theorem exists_flat_model_of_boundedAbove_model
    {B : Scheme.{u}}
    [hB : HasDerivedCategory (SheafOfModules.{u} (moduleRings B.toRingedSpace))]
    [hBM : HasDerivedCategory B.Modules]
    (E : schemeDerivedCategory B)
    (h : ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
      Nonempty (E ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :
    ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
      Nonempty (E ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) := by
  sorry

end AlgebraicGeometry
