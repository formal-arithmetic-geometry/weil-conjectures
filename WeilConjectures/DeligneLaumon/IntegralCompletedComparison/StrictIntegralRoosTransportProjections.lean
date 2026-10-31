/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.StrictIntegralRoosTransport

/-! # Finite projections of the recoded strict Roos comparison

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-strict-integral-roos-transport-projections).
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

/-- The recoded strict Roos model comparison preserves the specified finite projections.
This concerns the Roos model itself, before comparison with any derived finite tower.
Source: Stacks 0941 and 099N(5), 03EK/03EL; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-a1-strict-integral-roos-transport-projections).

Proof: choose an entire-tower K-injective resolution of the actual pulled reduction
of the good transported representative, with injective tower terms. Apply hq to
this resolution. Its normalized inclusion of the ordinary limit into the Roos
complex has nth first coordinate the ordinary limit projection and zero second
coordinate. The universal derived-limit unit identifies this coordinate with
completedReductionLimitProjection. Postcompose the model-matching identity with
the nth coordinate, use naturality along the resolution and cancel the localized
resolution map. The first-coordinate equation for the scalar Roos comparison z
identifies the resulting map with integralProjection. Transport back through the
two coefficient equivalences and their localization factors. The finite tower
isomorphism t in hq preserves the quotient augmentation. Quotient tensor-unit
generators determine its nth component; the normalization he and uniqueness of
the ordinary finite evaluation identify that component with the supplied e.
The normalized derived finite evaluation then identifies the two computation
counits. Reassociate their exact restriction factors to obtain the stated equation.
Only the actual nth coordinate is compared; finite evaluations are never used to
detect arbitrary derived morphisms. The argument also covers zero complexes and
empty sites, since all comparisons preserve the zero object and quotient units. -/
theorem strictIntegralRoosTransport_projections
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (i : PbcProperIntegralPullbackIdentification l E g)
    (q : integralDerivedPullback l E g ⋙ integralDetailedTransport X l E ≅
      integralDetailedTransport Y l E ⋙ completedReductionTower Y (pbcIntegralDatum l E) ⋙
        completedTowerPullback g (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) X)
    (hq : PbcProperIntegralModelMatching l E g i q)
    (e : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n)
    (he : ∀ n : ℕ, FiniteNormalization l E g n (e n))
    (P : CochainComplex
      (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
    (n : ℕ) :
    (strictIntegralRoosTransport l E g q).hom.app (DerivedCategory.Q.obj P) ≫
        integralProjection l E g P hP n ≫
          DerivedCategory.Q.map ((finiteComplexComparison l E g n (e n)).app P) =
      (derived l E X).map
        ((completedReductionLimitProjection (pbcIntegralDatum l E) (X := X) n).app
          ((completedTowerPullback g (pbcIntegralDatum l E)).obj
            ((completedReductionTower Y (pbcIntegralDatum l E)).obj
              (DerivedCategory.Q.obj P))) ≫
            (completedReductionFiniteEvaluation g (pbcIntegralDatum l E) n).hom.app
              (DerivedCategory.Q.obj P)) ≫ finiteComputation l E g P n := by
  sorry

end WeilConjectures.IntegralCompletedComparison
