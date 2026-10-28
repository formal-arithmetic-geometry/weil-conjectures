/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.IntegralPullbackRoosFiniteTower

/-! # Coefficient transport before the completeness restriction

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-strict-integral-coefficient-tower-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

/-- Transport the published strict completed tower before restricting its domain.
The supplied finite maps fix the ordinary generators; the supplied reflector
comparison is fixed by its unit. No completeness predicate enters this result.

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5);
sites-cohomology.tex, Tag 0941; derived.tex, Tags 011G and 014E.
(blueprint: lem-a1-strict-integral-coefficient-tower-transport).

Proof: use the projection-normalized coefficient equivalence on modules and
strict diagrams of modules. The quotient projections identify the source
reduction pair with the independent integral reduction pair. The completed
structural maps agree after every finite projection, hence agree as maps into
the completed coefficient limit. The ordinary pullbacks therefore have the
same scalar-extension adjunction after coefficient restriction. Their universal
derived counits give the corresponding comparison of derived strict pullbacks.
Compose with C.b, and take total right derived inverse limit. Exact coefficient
restriction is an equivalence, so it transports the total derived limit together
with its derived projections, giving b. For a good representative, C.zigzag
identifies the computation counit with the Koszul augmentation and the balanced
finite map. The supplied normalization of e identifies that balanced map with
the published finite evaluation, since both preserve every quotient-unit
generator. Apply the natural derived-limit projection to this identity; its
computation counit yields precisely the displayed equation, before composing
with any strict-to-reflector comparison.

The coefficient comparisons commute termwise with integer shifts. The
normalizations in C.reductionShift_descent, C.towerShift_descent and
C.finiteShift_descent identify their derived shifts with those termwise shifts.
The right-derived limit comparison has the same property by its universal unit.
The strict and reflector constructions are the same reflection with the same
quotient augmentation. Since a preserves that unit, reflector uniqueness
identifies a with this construction's comparison. Their unit-normalized shifts
therefore intertwine. The composite of a inverse, coefficient restriction, and b
is consequently a natural transformation commuting with all integer shifts,
with exactly the retained finiteTowerLimit shift. No detection of morphisms by
finite evaluations, nor exactness of ordinary completed pullback, is used. -/
theorem strictIntegral_coefficientTowerTransport
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (e : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n)
    (he : ∀ n : ℕ, FiniteNormalization l E g n (e n))
    (a : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E))
    (ha : ∀ K : PbcCompletedDerived Y (pbcIntegralDatum l E),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K ≫ a.hom.app K =
        (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K) :
    ∃ b : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙ derived l E X ≅
        finiteTowerLimit l E g C,
      (∀ (P : CochainComplex
          (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
        (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
        (n : ℕ),
        b.hom.app (DerivedCategory.Q.obj P) ≫ finiteTowerLimitProjection l E g C P n ≫
            DerivedCategory.Q.map ((finiteComplexComparison l E g n (e n)).app P) =
          (derived l E X).map
            ((completedReductionLimitProjection (pbcIntegralDatum l E) (X := X) n).app
              ((completedTowerPullback g (pbcIntegralDatum l E)).obj
                ((completedReductionTower Y (pbcIntegralDatum l E)).obj
                  (DerivedCategory.Q.obj P))) ≫
              (completedReductionFiniteEvaluation g (pbcIntegralDatum l E) n).hom.app
                (DerivedCategory.Q.obj P)) ≫ finiteComputation l E g P n) ∧
      NatTrans.CommShift (Functor.isoWhiskerRight a.symm (derived l E X) ≪≫ b).hom ℤ := by
  sorry

end WeilConjectures.IntegralCompletedComparison
