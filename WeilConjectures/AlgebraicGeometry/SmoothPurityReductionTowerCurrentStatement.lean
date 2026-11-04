/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized

/-!
# The reduction tower of a complex is normalized

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-coefficients/sk-prop-sp-integral-towers/
`det-sp-reduction-tower-normalized`, full statement.
(blueprint: det-sp-reduction-tower-normalized).

The theorem states the canonical derived reduction tower for arbitrary schemes,
and its normalized constructible finite-Tor conclusion for Noetherian schemes
on which the fixed prime is invertible. The construction is represented by the
record `SpReductionTowerConstruction`; its fields expose the derived reductions, quotient
transitions, functoriality, and normalization maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Construction of the canonical derived reduction tower, without a constructibility
hypothesis or conclusion. The quotient transitions and K-flat computation characterize
its functor into the ordinary derived category of strict coefficient towers.

Source: blueprint latest, integral-towers-reduction, Construction
(blueprint: det-sp-reduction-tower-normalized). -/
structure SpReductionTowerConstruction (D : SpCoefficientTowersAbelian l E T) where
  /-- The pulled-back integral ring identified with its completed section-ring model. -/
  coefficient : spIntegralSectionRing l E T ≅
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T
  /-- The comparison agrees with the canonical inverse-limit comparison on sections. -/
  coefficient_normalized : ∀ (U : T.ProEtᵒᵖ)
    (x : (condensedRingObj (spIntegralCondensed l E) T).obj.obj U),
    coefficient.hom.hom.app U x = (spIntegralAbComparison l E T).hom.hom.app U x
  /-- Ordinary coefficient reduction with values in strict coefficient towers. -/
  ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T
  /-- Ordinary tensor extension is additive. -/
  [additive : ordinary.Additive]
  /-- Its positive levels are the existing sheafified scalar extensions. -/
  level : spReductionOrdinaryLevels l E T D coefficient ordinary
  /-- Quotient-induced transitions, specified on local pure tensors. -/
  transition : IsSpReductionTransition l E T D coefficient ordinary level
  /-- Reduction on the ordinary unbounded derived categories. -/
  red : DerivedCategory (spIntegralSectionModules l E T) ⥤
    spDerivedCoefficientTowers l E T D
  /-- The localization comparison with degreewise ordinary reduction. -/
  counit : DerivedCategory.Q ⋙ red ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l E T D
  /-- The universal left derived functor of the specified ordinary reduction. -/
  universal : red.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (spIntegralSectionModules l E T) (.up ℤ))
  /-- K-flat representatives compute the canonical reduction. -/
  computes : ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
      IsIso (counit.app P)
  /-- Every derived evaluation is the actual derived quotient extension. -/
  evaluation : spReductionDerivedEvaluations l E T D coefficient red

set_option linter.unusedVariables false in
/-- The canonical reduction tower exists and is normalized; under Noetherianity and
stalkwise invertibility of `l`, every bounded constructible integral complex gives a
normalized constructible finite-Tor tower with the same Tor bounds.

Source: blueprint latest, `det-sp-reduction-tower-normalized`, construction and
normalization for arbitrary `T`, and constructibility under Noetherian `T` with `l`
invertible (blueprint: det-sp-reduction-tower-normalized).

The proof follows the source construction: identify the completed integral
coefficient sheaf with the inverse limit of its `l`-power quotients; descend
K-flat tensoring to a functorial tower and evaluate it levelwise; identify
successive derived quotients with the quotient-induced transitions; then use the
integral criterion, finite local models, open/closed refinement, and Tor
comparison to obtain uniform finite-level constructibility and Tor bounds. -/
theorem sp_reduction_tower_current_statement
    (D : SpCoefficientTowersAbelian l E T) :
    ∃ r : SpReductionTowerConstruction l E T D,
      (∀ M : DerivedCategory (spIntegralSectionModules l E T),
        IsSpNormalizedTower l E T D (r.red.obj M)) ∧
      (∀ [hN : IsNoetherian T],
        ∀ (hℓ : ∀ x : T, IsUnit (l : T.presheaf.stalk x)),
        ∀ M : DerivedCategory (spIntegralSectionModules l E T),
          constantModelBoundedConstructible (spIntegralCondensed l E) T
            ((spIntegralInternalization l E T).obj M) →
          DerivedCategory.finiteTorAmplitude _
            ((spIntegralInternalization l E T).obj M) ∧
          spNormalizedConstructibleTorTowers l E T D (r.red.obj M) ∧
          ∀ (a b : ℤ), a ≤ b →
            DerivedCategory.torAmplitudeIn _ a b
              ((spIntegralInternalization l E T).obj M) →
            ∀ n : ℕ,
              Scheme.HasProEtaleTorAmplitude T
                (Padic.coefficientExtensionIntegers l E ⧸
                  spEllIdeal l E ^ (n + 1))
                ((spDerivedCoefficientEvaluation l E T D n).obj (r.red.obj M)) a b ∧
              ∀ i : ℤ, (i < a ∨ b < i) → IsZero
                ((@DerivedCategory.homologyFunctor
                  (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
                    (Padic.coefficientExtensionIntegers l E ⧸
                      spEllIdeal l E ^ (n + 1))))
                  _ _ (HasDerivedCategory.standard _) i).obj
                  ((spDerivedCoefficientEvaluation l E T D n).obj (r.red.obj M)))) := by
  obtain ⟨R⟩ := sp_reduction_tower_normalized l E T D
  refine ⟨{
    coefficient := R.coefficient
    coefficient_normalized := R.coefficient_normalized
    ordinary := R.ordinary
    additive := R.additive
    level := R.level
    transition := R.transition
    red := R.red
    counit := R.counit
    universal := R.universal
    computes := R.computes
    evaluation := R.evaluation }, R.normalized, ?_⟩
  intro _ _ M hM
  exact R.constructible inferInstance inferInstance M hM

end AlgebraicGeometry.ProEtale
