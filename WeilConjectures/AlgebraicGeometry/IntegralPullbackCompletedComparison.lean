/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.CompletedPullbackTriangles
public import WeilConjectures.AlgebraicGeometry.SfImmersionCompletedPullbackComparison
public import WeilConjectures.AlgebraicGeometry.CompletedPullbackReduction
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackShiftCoordinates
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackCompletedComparisonData
import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.IntegralPullbackSignedShift
import WeilConjectures.AlgebraicGeometry.CompletedIntegralFiniteTowerTransport

/-! # Integral and strict-tower completed pullback

Source: Stacks Project, proetale.tex, Tag 099N(5), with sites-cohomology.tex,
Tag 0941 (blueprint: lem-a1-integral-pullback-completed-comparison).

The coefficient transport is the existing projection-normalized ring isomorphism.
Finite comparisons below are fixed on inverse-image generators; the integral
projections are the actual mapping-cocone projections on K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private instance (priority := 3000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W

private instance (priority := 3000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

namespace WeilConjectures.IntegralCompletedComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)


attribute [local irreducible] pbcIntegralDatum

private theorem quotientEquiv_eq (n : ℕ) :
    ImmersionCompletedPullback.quotientEquiv l E n = integralCoefficientULift l E n := by
  exact (ImmersionCompletedPullback.quotientEquiv_exists l E n).unique
    (ImmersionCompletedPullback.quotientEquiv_exists l E n).exists.choose_spec
    (integralCoefficientULift_exists l E n).exists.choose_spec

private theorem coefficientIso_eq (T : Scheme.{u}) :
    (adicLisseForget T).mapIso (ImmersionCompletedPullback.completedRingIso l E T) =
      integralDetailedCoefficientComparison T l E := by
  apply (integralDetailedCoefficientComparison_exists T l E).unique
    ?_ (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec
  intro n
  have h := congrArg (fun f ↦ (adicLisseForget T).map f)
    ((ImmersionCompletedPullback.completedRingIso_exists l E T).exists.choose_spec n)
  have hp : (adicLisseForget T).map
      (completedIntegralCommRingProjectionUnrestricted l E T n) =
      limit.π (integralCoefficientSheafSystem l E T) (op n) := by
    rfl
  simpa only [Functor.map_comp, Functor.mapIso_hom, hp,
    ImmersionCompletedPullback.completedRingIso,
    ImmersionCompletedPullback.finiteRingIso, integralDetailedLevelComparison,
    Iso.trans_hom, Functor.mapIso_trans, quotientEquiv_eq] using h

private theorem intrinsic_of_complete
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) (hK : Complete l E K) :
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K := by
  have hc : ImmersionCompletedPullback.completedRingIso l E Y = purCoefficientIso l E Y :=
    (purCoefficientIso_existsUnique l E Y).unique (coefficientIso_eq l E Y)
      (purCoefficientIso_existsUnique l E Y).exists.choose_spec
  apply (purCoefficientModel_predicates l E Y K).1.mpr
  simpa only [Complete, derived, ImmersionCompletedPullback.transport, hc,
    purCoefficientModel, Equivalence.changeFunctor] using hK

private theorem completedToFiniteTower_naturality
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (b : transportedStrict l E g ≅ finiteTowerLimit l E g C)
    (K L : PbcCompletedDerived Y (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K)
    (hL : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) L) (f : K ⟶ L) :
    (completed l E g).map f ≫ (completedToFiniteTower l E g C b L hL).hom =
      (completedToFiniteTower l E g C b K hK).hom ≫
        (finiteTowerLimit l E g C).map f := by
  change (derived l E X).map ((pbcActualCompletedPull g (pbcIntegralDatum l E)).map f) ≫
      ((derived l E X).map ((towerIso l E g).inv.app ⟨L, hL⟩) ≫ b.hom.app L) =
    ((derived l E X).map ((towerIso l E g).inv.app ⟨K, hK⟩) ≫ b.hom.app K) ≫ _
  rw [← Functor.map_comp_assoc]
  have h := (towerIso l E g).inv.naturality
    (ObjectProperty.homMk f :
      (⟨K, hK⟩ : ObjectProperty.FullSubcategory
        (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))) ⟶
        ⟨L, hL⟩)
  change (pbcActualCompletedPull g (pbcIntegralDatum l E)).map f ≫ _ =
    _ ≫ (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).map f at h
  rw [h, Functor.map_comp, Category.assoc]
  simpa only [transportedStrict, Functor.comp_map, Category.assoc] using congrArg
    ((derived l E X).map ((towerIso l E g).inv.app ⟨K, hK⟩) ≫ ·)
    (b.hom.naturality f)

private theorem conjugate_shift_square
    {A : Type*} [Category A] [HasShift A ℤ]
    {I J H Ir Jr Hr : A} (a : I ≅ H) (ar : Ir ≅ Hr)
    (b : J ≅ H) (br : Jr ≅ Hr) (r : ℤ)
    (i : Ir ⟶ I⟦r⟧) (j : Jr ⟶ J⟦r⟧) (h : Hr ⟶ H⟦r⟧)
    (ha : ar.hom ≫ h = i ≫ a.hom⟦r⟧')
    (hb : br.hom ≫ h = j ≫ b.hom⟦r⟧') :
    (ar ≪≫ br.symm).hom ≫ j = i ≫ (a ≪≫ b.symm).hom⟦r⟧' := by
  apply (cancel_mono (b.hom⟦r⟧')).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← hb]
  simp only [← Category.assoc]
  simpa only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, Category.comp_id] using ha

/-- Integral derived pullback agrees naturally with strict-tower completed pullback,
including the intrinsic domain, all finite derived-limit projections and every shift.
The two coefficient presentations are related by the already recorded unique
projection-normalized completed-ring isomorphism, not an extra hypothesis on K.
Source: Stacks Project, proetale.tex, Tag 099N(5), and sites-cohomology.tex, Tag 0941
(blueprint: lem-a1-integral-pullback-completed-comparison).

Proof:
1. Projection-normalized uniqueness identifies the completed coefficient-ring
   comparison with the coefficient model used by integral completeness. The
   coefficient-completeness transport therefore gives intrinsic completeness.
2. Use the finite-pullback strict-tower comparison C. Its termwise normalized
   shifts give the signed Roos shift, which descends along good complexes.
3. Realize integral Roos pullback as H, the total derived limit of C.B. Independently,
   transport the published strict completed tower to H by the coefficient-ring
   isomorphisms, retaining its finite quotient-unit normalizations.
4. On a complete K, compose the integral-to-H comparison with the inverse of the
   actual-completed-to-H comparison. Naturality follows from the naturality of
   both maps and cancellation. Compose their two representative projection
   identities to obtain precisely the required projection formula.
5. The two realization comparisons intertwine their specified shifts with H's
   shift. Conjugating these two squares gives the required square for gamma.
   Shift stability supplies the completeness proof for K[r].
-/
theorem integralPullback_completedComparison
    (g : X ⟶ Y) (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Comparison l E g) := by
  obtain ⟨C⟩ := FinitePullbackStrictTower.finite_pullback_strict_tower_comparison.{u, u}
    l E g _hX _hY
  obtain ⟨c, d, hc, hd⟩ := integralPullback_signedShift.{u} l E g C
  obtain ⟨a, ha, hshift⟩ := integralPullback_roosFiniteTower.{u} l E g C c hc d hd
  obtain ⟨e, b, he, hb, hbs⟩ :=
    completedIntegral_finiteTowerTransport.{u} l E g _hX _hY C
  let intrinsic : ∀ (K : PbcCompletedDerived Y (pbcIntegralDatum l E)),
      Complete.{u} l E K → PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K :=
    intrinsic_of_complete.{u} l E (Y := Y)
  let beta (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) (hK : Complete.{u} l E K) :
      (completed.{u} l E g).obj K ≅ (finiteTowerLimit.{u} l E g C).obj K :=
    completedToFiniteTower.{u} l E g C b K (intrinsic K hK)
  let gamma (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) (hK : Complete.{u} l E K) :
      (integral.{u} l E g).obj K ≅ (completed.{u} l E g).obj K :=
    a.app K ≪≫ (beta K hK).symm
  refine ⟨(show Comparison.{u} l E g from {
    intrinsic := intrinsic
    finite := e
    finite_normalization := he
    chainShift := c
    chainShift_coordinates := hc
    derivedShift := d
    derivedShift_descent := hd
    gamma := gamma
    naturality := ?_
    projections := ?_
    shifts := ?_ })⟩
  · intro K L hK hL f
    apply (cancel_mono (beta L hL).hom).mp
    simp only [gamma, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [completedToFiniteTower_naturality.{u} l E g C b K L
      (intrinsic K hK) (intrinsic L hL) f]
    change (integral l E g).map f ≫ a.hom.app L =
      a.hom.app K ≫ (beta K hK).inv ≫ (beta K hK).hom ≫
        (finiteTowerLimit l E g C).map f
    simpa only [Iso.inv_hom_id_assoc] using a.hom.naturality f
  · intro P hP hK n
    have hp : a.hom.app (DerivedCategory.Q.{u + 2}.obj P) ≫
        finiteTowerLimitProjection.{u} l E g C P n = integralProjection.{u} l E g P hP n :=
      ha P hP n
    have hpi : a.inv.app (DerivedCategory.Q.{u + 2}.obj P) ≫
        integralProjection.{u} l E g P hP n = finiteTowerLimitProjection.{u} l E g C P n := by
      rw [← hp]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    change ((beta (DerivedCategory.Q.obj P) hK).hom ≫
      a.inv.app (DerivedCategory.Q.{u + 2}.obj P)) ≫ _ ≫ _ = _
    simp only [Category.assoc]
    rw [← Category.assoc (a.inv.app (DerivedCategory.Q.{u + 2}.obj P)), hpi]
    exact hb P hP (intrinsic _ hK) n
  · let := d
    let : NatTrans.CommShift a.hom ℤ := hshift
    intro K hK r
    obtain ⟨hKr, hbr⟩ := hbs K hK r
    refine ⟨hKr, ?_⟩
    exact conjugate_shift_square (a.app K) (a.app (K⟦r⟧))
      (beta K hK) (beta (K⟦r⟧) hKr) r
      (((integral l E g).commShiftIso r).hom.app K)
      (((completed l E g).commShiftIso r).hom.app K)
      (((finiteTowerLimit l E g C).commShiftIso r).hom.app K)
      ((NatTrans.shift_app_comm a.hom r K).symm)
      (hbr (intrinsic K hK) (intrinsic (K⟦r⟧) hKr))

end WeilConjectures.IntegralCompletedComparison
