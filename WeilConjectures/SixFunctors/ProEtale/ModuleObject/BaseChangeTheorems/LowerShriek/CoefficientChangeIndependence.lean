/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral

/-!
# The independence isomorphisms of the lower shriek through the chosen refinements

The isomorphisms `Rf_!^{c₁} ≅ Rf_!^{c₂}` between the lower shrieks of two compactifications, for
`E`-sheaves (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso`) and
for `𝒪_E`-sheaves
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers`),
are composites of the isomorphisms `ProEtale.CondensedRing.boundedConstructibleLowerShriekRefinementIso`
along the refinements chosen by `Compactification.exists_overRefinement`. This file records these
unfoldings, which are used to compare them along a change of coefficients.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- Unfolding `boundedConstructibleLowerShriekOfCompactificationIso`: the comparison through the
chosen common refinement. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso_eq_refinementIso
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (c₁ c₂ : Compactification f.left) :
    haveI := (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isProper
    haveI := (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isProper
    haveI := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E
      (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
    haveI := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E
      (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
    boundedConstructibleLowerShriekOfCompactificationIso ℓ E c₁ c₂ =
      boundedConstructibleLowerShriekRefinementIso _ ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.hom_overG ≪≫
        (boundedConstructibleLowerShriekRefinementIso _ ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.hom_overG).symm := by
  unfold boundedConstructibleLowerShriekOfCompactificationIso
  rfl

/-- Unfolding `boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers`: the
comparison through the chosen common refinement. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers_eq_refinementIso
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (c₁ c₂ : Compactification f.left) :
    haveI := (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isProper
    haveI := (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isProper
    haveI := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers
      ℓ E (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
    haveI := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers
      ℓ E (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
    boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E c₁ c₂ =
      boundedConstructibleLowerShriekRefinementIso _ ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.hom_overG ≪≫
        (boundedConstructibleLowerShriekRefinementIso _ ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.hom_overG).symm := by
  unfold boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
