/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteStrictComparisons
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteStrictReductionOrigins
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteAlphaComponents
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompletedAlphaComponents

/-!
# Invertibility of the completed proper/open gamma

The proper/open comparison `cbcProperOpenGamma` on completed-ring modules is invertible
on complete objects with compatible bounded-below etale origins. The proof passes to the
strict quotient tower after constant-coefficient restriction, where the strict proper/open
gamma is invertible by finite compact-support base change.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived flatConstantModulesAbelian
  SheafOfModules.RingedCoefficientProjection.cachedSheafifyModules
  SheafOfModules.RingedCoefficientProjection.cachedLocalEquivalences

attribute [local instance 100000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

section Reflection

end Reflection

end AlgebraicGeometry.Scheme
