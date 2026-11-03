/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientRefinementExchange
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions

/-! Constructibility of the ordinary finite quotient used in closed exchange.
(blueprint: lem-sp-original-integral-finite-quotient-constructible)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

/-- The positive ordinary quotient is constructible.

Source: Bhatt--Scholze, Section 6.1; the closure of constructibility under cokernels.
Proof: apply the cokernel closure theorem to scalar multiplication on the given
constructible module.
(blueprint: lem-sp-original-integral-finite-quotient-constructible) -/
theorem originalIntegralFiniteQuotientConstructible
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X) M)
    (n : ℕ) :
    IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)
      (cokernel (ell ^ (n + 1) • 𝟙 M)) := by
  apply (constructible_cokernels_extensions X
    (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)).1.cokernels_le
  exact (CategoryTheory.MorphismProperty.cokernels.of_isColimit
    (ell ^ (n + 1) • 𝟙 M) (CokernelCofork.ofπ (cokernel.π _)
      (cokernel.condition _)) (cokernelIsCokernel _) ⟨hM, hM⟩)

end AlgebraicGeometry.ProEtale.CondensedRing
