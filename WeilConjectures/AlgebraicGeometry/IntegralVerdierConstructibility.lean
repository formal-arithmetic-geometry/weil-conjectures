/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement

/-! # Integral constructibility in the spectral coefficient presentation

Source: thm-coef-integral-verdier.proof.md, first paragraph, identification
of the input category by the integral criterion.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint

attribute [local irreducible] pointIntegerIso

/-- Native constructibility and finite constant local models agree over the
spectral integral coefficient ring. The boundedness predicate is identical.
Source: latest blueprint thm-coef-integral-verdier.proof.md, first paragraph;
input category of the integral criterion
(blueprint: lem-coef-integral-verdier-constructibility).

Proof: the WithAbs ring equivalence is an isometry of integer rings, hence gives
an isomorphism of condensed coefficient rings. Restriction of scalars along it
preserves native and constant-model constructibility. Apply the integral
local-finite-presentation comparison to obtain equivalence degree by degree.
The reverse implication uses the same scalar presentations on each stratum.
Conjoin with the common derived boundedness predicate. Zero objects and empty
stratifications require no extra assumptions. -/
theorem integralVerdier_constructibility
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    boundedConstructible (condensedRingObj (DerivedNakayama.integerRing l E) X) =
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X := by
  funext K
  apply propext
  exact and_congr Iff.rfl (forall_congr' fun n ↦ integerConstructibleComparison l E X _)

end AlgebraicGeometry.ProEtale
