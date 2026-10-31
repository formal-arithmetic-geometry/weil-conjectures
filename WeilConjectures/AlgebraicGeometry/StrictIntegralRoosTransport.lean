/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralPullbackCompletedComparisonData
public import WeilConjectures.AlgebraicGeometry.ProperIntegralOrdinaryData
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransportSupplement
import all WeilConjectures.AlgebraicGeometry.SfImmersionCompletedPullbackComparison

/-! # Recoding the normalized strict Roos comparison

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: def-a1-strict-integral-roos-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Both exact coefficient restrictions use the projection-normalized ring isomorphism.
Source: Bhatt--Scholze Section 6.5; Stacks 099N.
(blueprint: lem-a1-strict-integral-coefficient-model-equality).

Proof: the two completed ring isomorphisms have the same finite quotient projections.
Their uniqueness identifies them, and hence the induced exact derived restrictions. -/
theorem strictIntegralCoefficientModel_eq (W : Scheme.{u}) :
    (purCoefficientModel l E W).functor = derived l E W := by
  change pbcDerivedRestrict (purCoefficientIso l E W).inv =
    pbcDerivedRestrict (ImmersionCompletedPullback.completedRingIso l E W).inv
  rw [ImmersionCompletedPullback.completedRingIso_eq]

/-- Recode a specified strict Roos model comparison in the coefficient presentation
of the finite-tower interface. This construction makes no choice of a comparison.
Source: Stacks 03D3, 0941; Bhatt--Scholze Remark 6.8.15.
(blueprint: def-a1-strict-integral-roos-transport).

Construction: move the source coefficient equivalence across q inverse, reassociate,
and move the target inverse equivalence across the result. Identify the two exact
restriction models by their normalized coefficient ring isomorphisms. The final
associator preserves the published association of the strict completed pullback. -/
def strictIntegralRoosTransport
    (q : integralDerivedPullback l E g ⋙ integralDetailedTransport X l E ≅
      integralDetailedTransport Y l E ⋙ completedReductionTower Y (pbcIntegralDatum l E) ⋙
        completedTowerPullback g (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) X) :
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙ derived l E X ≅
      integral l E g := by
  let v := Iso.isoInverseComp (G := (purCoefficientModel l E Y).symm) q.symm
  let w := v ≪≫ (Functor.associator (purCoefficientModel l E Y).functor
    (integralDerivedPullback l E g) (integralDetailedTransport X l E)).symm
  let z := Iso.compInverseIso (H := (purCoefficientModel l E X).symm) w
  let z₀ := Functor.isoWhiskerRight
    (Functor.associator (completedReductionTower Y (pbcIntegralDatum l E))
      (completedTowerPullback g (pbcIntegralDatum l E))
      (completedTowerRlim (pbcIntegralDatum l E) X)) (derived l E X)
  let T := completedReductionTower Y (pbcIntegralDatum l E) ⋙
    completedTowerPullback g (pbcIntegralDatum l E) ⋙ completedTowerRlim (pbcIntegralDatum l E) X
  let hX := strictIntegralCoefficientModel_eq l E X
  let hY := strictIntegralCoefficientModel_eq l E Y
  exact z₀ ≪≫ Functor.isoWhiskerLeft T (eqToIso hX.symm) ≪≫
    z ≪≫ Functor.isoWhiskerRight (eqToIso hY) (integralDerivedPullback l E g)


end WeilConjectures.IntegralCompletedComparison
