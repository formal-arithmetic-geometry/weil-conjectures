/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelRealizationData
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelRealizationCoherence

/-! # Normalized realization of a single coefficient tower

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The fixed constant-scalar realization exists for any supplied evaluation package.
Source: Zheng, Construction 4.1; Stacks 03CY and 06YY. -/
theorem etaleBrownLevelRealization_exists
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) :
    Nonempty (StrictEtaleBrownRealization O t W P) := by
  obtain ⟨R⟩ := etaleBrownLevelRealizationData_exists O t W P
  exact etaleBrownLevelRealizationCoherence_exists O t W P R

end AlgebraicGeometry
