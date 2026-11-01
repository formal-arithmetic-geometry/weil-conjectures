/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
public import WeilConjectures.ProEtaleCoefficients.PrincipalConeTensorNormalization
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! Completeness of integral internal Hom in its second variable.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-integral-hom-reduction.proof.md, final two paragraphs.
(blueprint: lem-coef-integral-hom-reduction-completeness).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedIntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- If `L` is derived complete, so is the integral internal Hom `Hom(K,L)`, for arbitrary `K`.

Source: blueprint proof of lem-coef-integral-hom-reduction, second and third paragraphs
(blueprint: lem-coef-integral-hom-reduction-completeness).

Proof:
1. As `L` is complete, its Roos triangle
   `L → prod_n L_(n+1) --(1 - s)--> prod_n L_(n+1) → L[1]` is distinguished, the first map having
   the canonical reductions as components (`isDerivedComplete_iff`, derived limits).
2. `Hom(K,-)` is triangulated and, as a right adjoint of the derived tensor, preserves products;
   it carries this triangle to a distinguished triangle on `Hom(K,L)` with components
   `Hom(K, L → L_(n+1))` and transitions `Hom(K, L_(n+2) → L_(n+1))`.
3. The finite-free cone isomorphisms `theta_n : Hom(K,L) tensor A_(n+1) ≅ Hom(K, L_(n+1))` (step 2
   of `comparison_isIso`) commute with the maps from `Hom(K,L)` and with the transitions, so they
   carry this triangle to the Roos triangle of the reductions of `Hom(K,L)`, with the canonical
   reduction as first map. Hence the completion map of `Hom(K,L)` is invertible, which is
   `IsDerivedComplete`. -/
theorem derivedHom_isDerivedComplete
    (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    IsDerivedComplete l E X L →
      IsDerivedComplete l E X
        (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralHom
