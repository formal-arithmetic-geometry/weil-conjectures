/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentationExists
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentationUnique

/-! # The finite strict completed Koszul tensor augmentation

Source: Stacks Project, Tags 091N and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

/-- There is a uniquely normalized strict augmentation before taking any products.
The second clause prescribes zero on every summand of nonzero exterior degree.
There is no K-flatness, pro-zero, inverse-limit, or Roos assertion here. -/
theorem completedKoszulTensorQuotientAugmentation
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃! β : completedKoszulTensorTower T d r a ⟶
        (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ),
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
        completedAdicKoszulTensorUnit T d r a P n ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app (op n) =
            completedQuotientTensorUnit T d P n) ∧
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        completedKoszulTensorSummand T d r a P n p q ≫
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
              (β.app P)).app (op n)).f (p + q) = 0) := by
  obtain ⟨β, hβ⟩ := completedKoszulTensorQuotientAugmentation_exists T d r a ha
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  exact (completedKoszulTensorQuotientAugmentation_unique T d r a β γ hβ hγ).symm

end AlgebraicGeometry.Scheme
