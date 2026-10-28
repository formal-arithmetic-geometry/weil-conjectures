module

public import Sheaf.SixFunctors.OpenTensorQuotientData

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The objectwise comparison underlying strict-system scalar compatibility.
Source: Stacks Project, Tags 03DI, 03DJ and 0941.
(blueprint: lem-sf-open-quotient-scalar-system-components).
-/
theorem openQuotientScalarSystemsComponents
    (o : IntegralOpenReduction.Operations l E j) :
    Nonempty (∀ C : CochainComplex (coefficientSequenceModules l E U) ℤ,
      ((IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ) ⋙
          forgetSystems l E X).obj C ≅
        (forgetSystems l E U ⋙ extendTower l E j o).obj C) := by
  sorry

end WeilConjectures.OpenTensorQuotient
