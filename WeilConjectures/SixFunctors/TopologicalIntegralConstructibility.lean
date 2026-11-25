/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators

/-! Constructibility of a single integral locally closed extension in the topological
Noetherian setting.

## References

* Bhatt--Scholze, Lemma 6.8.13
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.SixFunctors

/-- The integral extension by zero `i_* j_! L₀` of a locally finite free `O_E`-module is
constant-model constructible on a topologically Noetherian scheme. -/
theorem topological_integral_extension_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (T Z : Scheme.{u}) (j : T ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (L₀ : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (integralCoefficientObject T ℓ E))
    (hL₀ : CondensedRing.LocallyFree (integralCoefficientObject T ℓ E) L₀) :
    IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
      (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) j i L₀) := by
  sorry

end WeilConjectures.SixFunctors
