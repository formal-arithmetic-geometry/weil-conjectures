/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralPullbackRoosFiniteTower
import WeilConjectures.AlgebraicGeometry.FiniteIntegralCoefficientComparison
import WeilConjectures.AlgebraicGeometry.StrictIntegralCoefficientTowerTransport
import all WeilConjectures.AlgebraicGeometry.PbcActualStrictPullback
import all WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActualSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.SfImmersionCompletedPullbackComparison

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

private theorem strictActualComparison :
    ∃ a : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ≅
        pbcActualCompletedPull g (pbcIntegralDatum l E),
      ∀ K : PbcCompletedDerived Y (pbcIntegralDatum l E),
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K ≫ a.hom.app K =
          (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K := by
  let d := pbcIntegralDatum l E
  classical
  let L := pbcActualDerivedPull g d
  let R := completedTowerRlim d X
  let eL := pullbackDatumOrdinaryTransport g d
  let eT := pullbackDatumTowerTransport g d
  let τ := stratumReductionIso d g
  let t : completedReductionTower Y d ⋙ completedTowerPullback g d ≅
      L ⋙ completedReductionTower X d :=
    Functor.isoWhiskerLeft (completedReductionTower Y d) eT ≪≫ τ ≪≫
      Functor.isoWhiskerRight eL.symm (completedReductionTower X d)
  have ht (K : PbcCompletedDerived Y d) :
      ((completedPullbackConstantIso g d).hom.app K ≫
        (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) ≫
          t.hom.app K = (completedReductionTowerUnit d X).app (L.obj K) := by
    exact reductionAugmentationTransport
      (completedDerivedConstant d Y) (completedDerivedConstant d X)
      (completedReductionTower Y d) (completedReductionTower X d)
      (completedOrdinaryPullback g d) (d.pull g)
      (completedTowerPullback g d) (d.towerPull g) eL eT
      (completedPullbackConstantIso g d) (d.derivedConstantPullbackIso g)
      (completedReductionTowerUnit d Y) (completedReductionTowerUnit d X) τ K
      (datumConstantComparison g d K) (stratumReduction_augmentation d g K)
  obtain ⟨c, hc⟩ := actualCompletion_quotient d X
  let b : pbcActualStrictCompletedPull d g ≅ pbcActualCompletedPull g d :=
    Functor.isoWhiskerRight t R ≪≫ Functor.associator L (completedReductionTower X d) R ≪≫
      Functor.isoWhiskerLeft L c.symm
  have hb (K : PbcCompletedDerived Y d) :
      (pbcActualStrictCompletedPullUnit d g).app K ≫ b.hom.app K =
        (pbcActualCompletedPullUnit g d).app K := by
    have hu : completedPullbackComparison g d K ≫ R.map (t.hom.app K) =
        d.completionUnit X (L.obj K) := by
      dsimp only [completedPullbackComparison]
      rw [Category.assoc, ← R.map_comp, ht, constantRlimUnit_eq]
      rfl
    simp only [pbcActualStrictCompletedPullUnit, pbcActualCompletedPullUnit, b,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.associator_hom_app, Functor.comp_obj, Iso.symm_hom]
    change completedPullbackComparison g d K ≫
      (R.map (t.hom.app K) ≫ c.inv.app (L.obj K)) =
        (pbcActualCompletionUnit d X).app (L.obj K)
    rw [← Category.assoc, hu, ← hc, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
  exact ⟨b, hb⟩

private theorem complete_shift
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) (hK : Complete l E K) (r : ℤ) :
    Complete l E (K⟦r⟧) := by
  apply (ImmersionCompletedPullback.transport_complete_iff l E Y (K⟦r⟧)).mp
  apply actualComplete_shift Y (pbcIntegralDatum l E) K
  exact (ImmersionCompletedPullback.transport_complete_iff l E Y K).mpr hK

set_option linter.unusedVariables false in
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
  obtain ⟨e, he⟩ := finiteIntegral_coefficientComparison l E g hX hY
  obtain ⟨a, ha⟩ := strictActualComparison l E g
  obtain ⟨b, hb, hs⟩ := strictIntegral_coefficientTowerTransport l E g hX hY C e he a ha
  have hrestriction :
      Functor.isoWhiskerLeft
          (ObjectProperty.ι (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))) a =
        towerIso l E g := by
    apply (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g).unique
    · intro K
      exact ha K.obj
    · exact (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g).exists.choose_spec
  let c : completed l E g ≅ finiteTowerLimit l E g C :=
    Functor.isoWhiskerRight a.symm (derived l E X) ≪≫ b
  have hcomponent (K : PbcCompletedDerived Y (pbcIntegralDatum l E))
      (hI : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K) :
      completedToFiniteTower l E g C b K hI = c.app K := by
    apply Iso.ext
    change (derived l E X).map ((towerIso l E g).inv.app ⟨K, hI⟩) ≫ b.hom.app K =
      (derived l E X).map (a.inv.app K) ≫ b.hom.app K
    rw [← hrestriction]
    rfl
  refine ⟨e, b, he, ?_, ?_⟩
  · intro P hP hK n
    change ((derived l E X).map ((towerIso l E g).inv.app ⟨_, hK⟩) ≫
      b.hom.app (DerivedCategory.Q.obj P)) ≫ _ ≫ _ = _
    simp only [Category.assoc]
    rw [hb P hP n]
    simp only [completedProjection, Functor.map_comp, Category.assoc]
  · have : NatTrans.CommShift c.hom ℤ := hs
    intro K hK r
    refine ⟨complete_shift l E K hK r, ?_⟩
    intro hI hIr
    rw [hcomponent (K⟦r⟧) hIr, hcomponent K hI]
    exact (NatTrans.shift_app_comm c.hom r K).symm


end WeilConjectures.IntegralCompletedComparison
