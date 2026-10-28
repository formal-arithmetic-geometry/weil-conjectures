/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorQuotientData

/-! # Finite-level scalar comparison data for an open quotient

Source: Stacks Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-finite-compatibility-generator).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Finite-level comparisons together with their naturality in modules.
The comparison is obtained on extension-by-zero generators by the identity on
sections and transported through the coefficient projection. Source: Stacks
Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-finite-compatibility-generator).
-/
structure FiniteScalarLevelData (o : IntegralOpenReduction.Operations l E j)
    (n : ℕ) where
  level : ∀ M : normalizedDVRModules l E U n,
    (scalarReductionRestriction l E X n).obj
      ((IntegralOpenReduction.finiteExtension l E j o n).obj M) ≅
      (scalarReductionRestriction l E U n ⋙
        IntegralOpenReduction.extension l E j o).obj M
  naturality : ∀ {M N : normalizedDVRModules l E U n} (f : M ⟶ N),
    ((IntegralOpenReduction.finiteExtension l E j o n ⋙
      scalarReductionRestriction l E X n).map f) ≫ (level N).hom =
      (level M).hom ≫ (scalarReductionRestriction l E U n ⋙
        IntegralOpenReduction.extension l E j o).map f

/-- The finite-level generator calculation supplies normalized comparison data.
Source: Stacks Project, Tags 03DI and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-finite-compatibility-generator).
-/
theorem finiteScalarLevelData_exists
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    Nonempty (FiniteScalarLevelData l E j o n) := by
  sorry

end WeilConjectures.OpenTensorQuotient
