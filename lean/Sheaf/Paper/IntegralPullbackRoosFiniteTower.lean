/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.IntegralPullbackCompletedComparisonData
public import Sheaf.Paper.FinitePullbackStrictTowerComparison


/-! # Integral Roos realization through the finite-tower derived pair

Source: Stacks Project, sites-cohomology.tex, Tag 0941, and proetale.tex, Tag 099N(5).
(blueprint: lem-a1-integral-roos-finite-tower-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory
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

/-- Total derived limit of the normalized finite pullback derived pair.
Source: Stacks 0941, 099N(5)
(blueprint: lem-a1-integral-roos-finite-tower-realization). -/
abbrev finiteTowerLimit (C : FinitePullbackStrictTower.Comparison.{u, u} l E g) :=
  (derived.{u} l E Y ⋙ C.B.functor) ⋙
    completedRlim.{u} X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)

/-- Its shift uses the retained finite-tower shift and the standard total-limit shift.
Source: Stacks 014E, 0941
(blueprint: lem-a1-integral-roos-finite-tower-realization). -/
instance finiteTowerLimit_commShift
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g) :
    (finiteTowerLimit l E g C).CommShift ℤ := by
  letI := C.finiteShift
  infer_instance

/-- The nth projection through the actual finite-tower computation counit.
The first factor accounts for exact completed-coefficient restriction on P.
Source: Stacks 0941, universal derived-limit projections
(blueprint: lem-a1-integral-roos-finite-tower-realization). -/
def finiteTowerLimitProjection (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :
    (finiteTowerLimit l E g C).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
          ((complexes l E Y).obj P)).obj (op n)) :=
  (completedRlim.{u} X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).map
      (C.B.functor.map ((modules l E Y).mapDerivedCategoryFactors.hom.app P) ≫
        C.B.counit.app ((complexes l E Y).obj P)) ≫
    (completedRlimProjection.{u} X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) n).app
      (DerivedCategory.Q.obj
        ((FinitePullbackStrictTower.finiteComplex.{u, u} l E g).obj
          ((complexes l E Y).obj P))) ≫
    (((evaluation ℕᵒᵖ (reductionModules X
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))).obj
          (op n)).mapDerivedCategoryFactors.hom.app
        ((FinitePullbackStrictTower.finiteComplex.{u, u} l E g).obj
          ((complexes l E Y).obj P)))

/-- The integral Roos construction realizes the total derived limit of its finite
pullback tower. This concerns the integral presentation alone, on every input;
it neither compares coefficient presentations nor uses intrinsic completeness.
Source: Stacks Project, sites-cohomology.tex, Tag 0941; proetale.tex, Tag 099N(5)
(blueprint: lem-a1-integral-roos-finite-tower-realization).
Proof: on a good representative P, the counit of C.B identifies its derived
finite tower with the localization of the actual strict finite pullback tower.
Transpose this tower to a complex of towers. Exact countable products give the
normalized strict Roos isomorphism from its product mapping fibre to the total
right derived inverse limit. Compose with the inverse of the limit of C.B's
counit. Both constructions are natural on good representatives. Their resolving
localization is fully faithful on functor categories, so the isomorphism descends
uniquely to the given integral pullback. The normalization on K-injective tower
resolutions identifies every projection with the first mapping-cocone coordinate
followed by the corresponding product leg. Apply this before and after the exact
coefficient restriction computation map to obtain the displayed equation for
all good P. The normalized Roos shift theorem gives the signed product-fibre shift;
C.finiteShift_descent and ShiftDescent identify its two descents, giving precisely
the CommShift equation, including the zero and addition laws. -/
theorem integralPullback_roosFiniteTower
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (hc : ShiftCoordinates l E g c)
    (d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ)
    (hd : ShiftDescent l E g c d) :
    ∃ a : integral l E g ≅ finiteTowerLimit l E g C,
      (∀ (P : CochainComplex
          (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
        (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
        (n : ℕ),
        a.hom.app (DerivedCategory.Q.obj P) ≫ finiteTowerLimitProjection l E g C P n =
          integralProjection l E g P hP n) ∧
      (fun [_d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ] ↦
        NatTrans.CommShift a.hom ℤ) (_d := d) := by
  sorry

end WeilConjectures.IntegralCompletedComparison
