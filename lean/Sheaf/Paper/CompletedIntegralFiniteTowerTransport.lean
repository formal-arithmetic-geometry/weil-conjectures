/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.IntegralPullbackRoosFiniteTower

/-! # Coefficient transport of the published completed pullback tower

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-completed-integral-finite-tower-transport).
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

/-- The published strict tower limit, after exact coefficient restriction.
Source: Stacks 099N(5)
(blueprint: lem-a1-completed-integral-finite-tower-transport). -/
abbrev transportedStrict :=
  pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙ derived l E X

/-- The canonical actual-to-strict comparison followed by coefficient transport.
No choice is made here: the tower comparison is the existing unit-normalized one.
Source: Stacks 099N(2),(5)
(blueprint: lem-a1-completed-integral-finite-tower-transport). -/
def completedToFiniteTower
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (b : transportedStrict l E g ≅ finiteTowerLimit l E g C)
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K) :
    (completed l E g).obj K ≅ (finiteTowerLimit l E g C).obj K :=
  (derived l E X).mapIso ((towerIso l E g).app ⟨K, hK⟩).symm ≪≫ b.app K

/-- Projection-normalized coefficient transport identifies the published pulled
quotient tower with the independent integral finite-tower model. The comparison
is built without reference to the integral Roos pullback or an isomorphism to it.
Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5)
(blueprint: lem-a1-completed-integral-finite-tower-transport).
Proof: the unique coefficient isomorphisms identify every positive quotient,
its transition and its quotient unit, and identify the two completed ring maps
by their finite projections. Thus exact restriction transports the published
reduction tower and ringed pullback to the independent-universe reduction pair
and derived tower pullback. The universal derived counits determine these
identifications on every objectwise K-flat representative, hence globally.
Apply the normalized finite-tower comparison C.b and take the total right derived
limit. Exact coefficient restriction is an equivalence, so it preserves that
right-derived pair and all its limit projections. This constructs b. At finite
level the balanced tensor map sends the quotient-unit generator to the same
finite generator. Its inverse inserts 1; sheafification and restriction preserve
these formulas. These maps give e with FiniteNormalization. The published finite
evaluation and C's zigzag are normalized by the same counits and generators;
their universal properties identify them. Applying the natural derived-limit
projection gives the displayed representative equality. Finally coefficient
restriction, the universal derived counits, C.b and total derived limit commute
with their retained shifts. The existing unit-compatible tower/reflector
comparison commutes with shifts by uniqueness, since both quotient units do.
Derived completeness is shift-stable. Their composite therefore has exactly the
stated square for every integer and every intrinsic-completeness proof. -/
theorem completedIntegral_finiteTowerTransport
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g) :
    ∃ (e : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n)
      (b : transportedStrict l E g ≅ finiteTowerLimit l E g C),
      (∀ n : ℕ, FiniteNormalization l E g n (e n)) ∧
      (∀ (P : CochainComplex
          (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
        (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
        (hK : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) (DerivedCategory.Q.obj P))
        (n : ℕ),
        (completedToFiniteTower l E g C b (DerivedCategory.Q.obj P) hK).hom ≫
            finiteTowerLimitProjection l E g C P n ≫
            DerivedCategory.Q.map ((finiteComplexComparison l E g n (e n)).app P) =
          completedProjection l E g (DerivedCategory.Q.obj P) hK n ≫
            finiteComputation l E g P n) ∧
      ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) (hK : Complete l E K) (r : ℤ),
        ∃ hKr : Complete l E (K⟦r⟧),
          ∀ (hI : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K)
            (hIr : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) (K⟦r⟧)),
          (completedToFiniteTower l E g C b (K⟦r⟧) hIr).hom ≫
              ((finiteTowerLimit l E g C).commShiftIso r).hom.app K =
            ((completed l E g).commShiftIso r).hom.app K ≫
              ((completedToFiniteTower l E g C b K hI).hom)⟦r⟧' := by
  sorry

end WeilConjectures.IntegralCompletedComparison
