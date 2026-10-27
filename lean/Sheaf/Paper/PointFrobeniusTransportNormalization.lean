/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65, SHEAF group G7
-/
module

public import Sheaf.Paper.PointFrobeniusNormalizationDefinitions
import Sheaf.Paper.PointQuotientComparisonCoordinates
import Sheaf.Paper.PointFiniteMultiplicationInverse
import Sheaf.Paper.PointIdentityExchangeRecipe
import Sheaf.TraceFormula.IsomorphismRoosUnitCancellation
import Sheaf.Paper.SfDerivedCompleteLegacyComparison

/-! Normalized point Frobenius transport, with its canonical coordinate vocabulary
reexported from PointFrobeniusNormalizationDefinitions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointFrobeniusNormalization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit frobeniusPointIso
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence FrobeniusExchange.models
  frobeniusPointRestriction integralOperationsRoosMap
private theorem isoCancellation {C : Type*} [Category C] {W X Y Z T : C}
    (a : W ≅ X) (b : Y ≅ Z) (c : Z ≅ T) (e : Y ≅ X) :
    ((a.hom ≫ e.inv ≫ b.hom) ≫ c.hom) ≫
      (c.symm ≪≫ b.symm ≪≫ e ≪≫ a.symm).hom = 𝟙 _ := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id]

private theorem transportCompose {C B : Type*} [Category C] [Category B]
    (F : C ⥤ B) {X Y Z : C} {T : B} (tau : T ⟶ F.obj Y) (sigma : T ⟶ F.obj X)
    (kappa : X ⟶ Y) (lambda : Y ⟶ X) (v : X ⟶ Z)
    (ht : tau = sigma ≫ F.map kappa) (hc : kappa ≫ lambda = 𝟙 X) :
    tau ≫ F.map (lambda ≫ v) = sigma ≫ F.map v := by
  calc
    _ = sigma ≫ F.map (kappa ≫ lambda) ≫ F.map v := by
      simp only [ht, F.map_comp, Category.assoc]
    _ = _ := by rw [hc, F.map_id, Category.id_comp]

private theorem coefficientCancel {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}}
    (c : R ⟶ S) [IsIso c] (U : Cᵒᵖ) (x : S.obj.obj U) :
    c.hom.app U ((inv c).hom.app U x) = x := by
  exact congrArg (fun f ↦ f.hom.app U x) (IsIso.inv_hom_id c)

private theorem inverseSection {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {K L : CochainComplex (SheafOfModules.{u + 1} R) ℤ}
    (e : K ≅ L) (i : ℤ) (U : Cᵒᵖ) (z : (K.X i).val.obj U) :
    (e.inv.f i).val.app U ((e.hom.f i).val.app U z) = z := by
  have h := congrArg (fun f ↦ (f.f i).val.app U z) e.hom_inv_id
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    SheafOfModules.comp_val, SheafOfModules.id_val, PresheafOfModules.comp_app,
    PresheafOfModules.id_app, ModuleCat.comp_apply, ModuleCat.id_apply] using h

private theorem tensorRestriction {X : Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    {U V : X.ProEt} (f : V ⟶ U) (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    ((SheafOfModules.siteSheafTensorRight N).obj M).val.map f.op
      (purTensorSection O M N U x y) =
        purTensorSection O M N V (M.val.map f.op x) (N.val.map f.op y) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).obj)
  exact (PresheafOfModules.naturality_apply
    (adj.unit.app (SheafOfModules.siteTensorPresheaf M.val N.val)) f.op (x ⊗ₜ[_] y)).symm

private theorem dualRestriction {X : Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    {U V : X.ProEt} (f : V ⟶ U)
    (φ : (SheafOfModules.homObj (R := O) M N).val.obj (op U))
    (x : M.val.obj (op U)) :
    N.val.map f.op (φ.app (op (Over.mk (𝟙 U))) x) =
      (((SheafOfModules.homObj (R := O) M N).val.map f.op φ).app
         (op (Over.mk (𝟙 V)))) (M.val.map f.op x) := by
  exact (PresheafOfModules.naturality_apply φ
    (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 U)).op x).symm

include hl in
private theorem restrictionScalarFix
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] (a : Option ℕ)
    (b : pointRestrictionScalars.{u, u} l E a) :
    (pointRestrictionCoefficientMap l E g a).hom.app (op (ProEt.mk (𝟙 _)))
      ((pointRestrictionRing l E (Spec (.of D.k)) a).obj.map (pointRestrictionArrow g).op
        (pointRestrictionScalarAt l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b)) =
      pointRestrictionScalarAt l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b := by
  have h := (point_automorphism_restriction_natural l E D hl g a).1 b
  exact (congrArg ((pointRestrictionCoefficientMap l E g a).hom.app
    (op (ProEt.mk (𝟙 _)))) h).trans
      (coefficientCancel (pointRestrictionCoefficientMap l E g a) _ _)

include hl in
private theorem tensorDual (a : Option ℕ) : TensorDualNormalization D l E a := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    exact restrictionScalarFix D l hl E (frobeniusPointIso D).hom a b
  · intro M N _ _ x y
    exact tensorRestriction (coefficientRing D l E a) M N (frobeniusPointRestriction D) x y
  · intro M N _ _ φ x
    exact dualRestriction (coefficientRing D l E a) M N (frobeniusPointRestriction D) φ x

attribute [local implicit_reducible] integralOperationsRoosFunctor integralOperationsRoos
private theorem roosAugmentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (a : (integralOperationsPullbackTowerFunctor l E g).obj P ⟶
      (trfInverseImageTower l E g).obj ((trfQuotientTowerFunctor l E Y).obj P))
    (e : (trfInverseImageComplex l E g).obj
        (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P)) ≅
      integralOperationsRoos ((trfInverseImageTower l E g).obj
        ((trfQuotientTowerFunctor l E Y).obj P)))
    (hj : TrfMultiplicationGeneratorNormalized l E g P a)
    (heta_fst : e.hom ≫ CochainComplex.mappingCocone.fst
        (trfInverseQuotientDifference l E g P) =
      (trfInverseImageComplex l E g).map
        (CochainComplex.mappingCocone.fst (trfQuotientDifference l E Y P)) ≫
      trfQuotientProductComparison l E g P)
    (heta_snd : ∀ p : ℤ, e.hom.f (p + 1) ≫
        (CochainComplex.mappingCocone.snd (trfInverseQuotientDifference l E g P)).v
          (p + 1) p (add_neg_cancel_right p 1) =
      (inverseImageIntegralModules l E g).map
        ((CochainComplex.mappingCocone.snd (trfQuotientDifference l E Y P)).v
          (p + 1) p (add_neg_cancel_right p 1)) ≫
      (trfQuotientProductComparison l E g P).f p) :
    inverseImageRoosComparisonComplex l E g P ≫ integralOperationsRoosFunctor.map a =
      (trfInverseImageComplex l E g).map
        (trfStrictQuotientConeAugmentation l E Y P) ≫ e.hom := by
  apply (Iso.comp_inv_eq e).mp
  exact (Category.assoc (inverseImageRoosComparisonComplex l E g P)
    (integralOperationsRoosFunctor.map a) e.inv).trans
      (isomorphismRoosUnitCancellation l E g P a e hj heta_fst heta_snd)


include hl in
private theorem quotientNormalization
    (M : integralTowerModules l E (Spec (.of D.k))) :
    IntegralQuotientNormalization D l E M := by
  intro P _
  let d := pointQuotientComparisonData D l hl E (frobeniusPointIso D).hom
    (calculus D l E) ((FrobeniusExchange.models l E).roos (Spec (.of D.k)))
  have hd : PointQuotientComparisonNormalized D l E (frobeniusPointIso D).hom d :=
    (pointQuotientComparison_exists D l hl E (frobeniusPointIso D).hom
      (calculus D l E) ((FrobeniusExchange.models l E).roos (Spec (.of D.k)))).choose_spec
  obtain ⟨hj₀, hjinv₀, hf₀, hs₀⟩ := hd
  let j := d.j.app P
  let eta := d.eta.app P
  have hj := hj₀ P
  have hjinv := hjinv₀ P
  have hf := hf₀ P
  have hs := hs₀ P
  refine ⟨j, ?_, hjinv, eta, hf, hs, ?_⟩
  · intro n i U x b
    let K := (unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj
    let kappa := inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n K
    have hspec := inverseImageFiniteComparison_existsUnique l E (frobeniusPointIso D).hom n K
    obtain ⟨e, hmul, hgen, hinv⟩ :=
      pointFiniteMultiplicationInverse D l hl E (frobeniusPointIso D).hom n K
    have hleft (z : (K.X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U))) :
        (((j.hom).app (op n)).f i).val.app (op U)
          ((kappa.f i).val.app (op U) z) = z :=
      (congrArg (fun y ↦ (((j.hom).app (op n)).f i).val.app (op U) y)
        (hspec.exists.choose_spec i U z)).trans (hj n i U z)
    have hright (z : (((integralOperationsLevelPullback l E
        (frobeniusPointIso D).hom n).obj (K.X i)).val.obj (op U))) :
        (kappa.f i).val.app (op U) ((e.hom.f i).val.app (op U) z) = z := by
      have he := inverseSection e i (op U) z
      exact (congrArg (fun f ↦ (f.f i).val.app (op U)
        ((e.hom.f i).val.app (op U) z)) hinv).trans he
    have hh := Function.LeftInverse.eq_rightInverse hleft hright
    exact Eq.trans (congrFun hh _) (hgen i U x b)
  · exact roosAugmentation l E (frobeniusPointIso D).hom P.obj
      j.hom eta hj hf hs

include hl in
private theorem integralComparison
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    ∃ θ : (integralDerivedPullback l E (frobeniusPointIso D).hom).obj N.obj ≅
        (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).obj
          (((calculus D l E).reduction ⋙
            coefficientSequenceLimit l E (Spec (.of D.k))).obj N.obj),
    ∃ ε : N.obj ≅ ((calculus D l E).reduction ⋙
        coefficientSequenceLimit l E (Spec (.of D.k))).obj N.obj,
      ε.hom = (calculus D l E).adjunction.unit.app N.obj ∧
      inverseImagePullbackComparisonDerived l E (frobeniusPointIso D).hom
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) N.obj ≫ θ.hom =
          (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).map ε.hom := by
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E (Spec (.of D.k))
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D₀ : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }
  have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
  have hN : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N.obj :=
    ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E (Spec (.of D.k)) D₀ hl₀ N.obj).mp
      N.property.1⟩
  obtain ⟨_, _, _, κinv, hleft, hright, _⟩ :=
    isomorphismDerivedPullbackComparisonNormalization l E
      (frobeniusPointIso D).hom (frobeniusPointPrimeUnit D l hl)
      (frobeniusPointPrimeUnit D l hl) S hS N.obj hN
  let G := inverseImageIntegralDerived l E (frobeniusPointIso D).hom
  let κ : G.obj N.obj ≅ (integralDerivedPullback l E (frobeniusPointIso D).hom).obj N.obj :=
    ⟨inverseImagePullbackComparisonDerived l E (frobeniusPointIso D).hom
      (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) N.obj,
      κinv, hright, hleft⟩
  let : IsIso ((calculus D l E).adjunction.unit.app N.obj) :=
    (FrobeniusExchange.models l E).complete (Spec (.of D.k)) N
  let ε := asIso ((calculus D l E).adjunction.unit.app N.obj)
  refine ⟨κ.symm ≪≫ G.mapIso ε, ε, rfl, ?_⟩
  change κ.hom ≫ κ.inv ≫ (G.mapIso ε).hom = _
  rw [← Category.assoc, κ.hom_inv_id, Category.id_comp]
  rfl


/-- Normalization of the specified point Frobenius comparisons and transport.
Source: blueprint main-20261015, def-weil-frobenius-coefficient-twists,
Natural Weil isomorphism; Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-point-frobenius-transport-normalization).

Proof:
1. Specialize pointFiniteMultiplicationInverse to the degree-zero complex.
   Its inverse is the specified finite comparison. Localize this identity with
   the exact-functor and intrinsic-pullback comparisons, then cancel their
   isomorphisms. Substitute pointIdentityExchangeRecipe and use functoriality
   to obtain the finite equation for every v.
2. Apply isomorphismMultiplicationConeDescent to the strict quotient tower.
   The specified generator equation identifies its hom as a left inverse of
   the finite comparison. The finite multiplication hom is a right inverse;
   uniqueness identifies these section functions and gives the scalar formula.
   The two cone coordinates and isomorphismRoosUnitCancellation give the whole
   augmentation equality, using explicit categorical associativity.
3. Convert intrinsic completeness to the legacy predicate, using an auxiliary
   universe-zero finite-field datum constructed explicitly from a prime p > l.
   The normalized whole-cone theorem supplies a two-sided inverse of kappa.
   The complete field of the recorded models makes the actual unit invertible.
   Define theta as inverse kappa followed by the image of this unit. Cancellation
   proves its normalization and then the integral kappa-lambda identity.
4. Substitute the integral identity-exchange recipe and compose with lambda
   and v. Apply the rational and closed coefficient functors to this equality.
5. Point restriction normalization gives the coefficient identity by cancelling
   the coefficient isomorphism. Tensor restriction is naturality of the
   sheafification unit on a pure tensor; dual evaluation is naturality of the
   local module map on the corresponding slice arrow. -/
theorem point_frobenius_transport_normalization :
    (∀ (n : ℕ) (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n),
      (∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free (ULift.{u + 1} (Fin r)))) →
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n)
        (Spec (.of D.k)) (DerivedCategory.Q.obj (finiteComplex D l E n M)) →
      FiniteNormalization D l hl E n M) ∧
    (∀ (M : integralTowerModules l E (Spec (.of D.k)))
      (hM : sfIntegralConstructible l E (Spec (.of D.k))
        (DerivedCategory.Q.obj (integralComplex D l E M))),
      (∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free (ULift.{u + 1} (Fin r)))) →
      IntegralNormalization D l hl E M hM) ∧
    (∀ a : Option ℕ, TensorDualNormalization D l E a) := by
  obtain ⟨hexFin, hrecipeFin, hexInt⟩ := pointIdentityExchangeRecipe D l hl E
  refine ⟨?_, ?_, tensorDual D l hl E⟩
  · intro n M _ _
    obtain ⟨e, hmul, _, hinv⟩ := pointFiniteMultiplicationInverse D l hl E
      (frobeniusPointIso D).hom n (finiteComplex D l E n M)
    let : (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).Additive := by
      with_unfolding_all
        exact isoSectionwiseModuleInverseImage_additive (frobeniusPointIso D).hom
          (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)
    let : PreservesFiniteLimits (inverseImageFiniteModules l E (frobeniusPointIso D).hom n) := by
      with_unfolding_all
        exact isoSectionwiseModuleInverseImage_limits (frobeniusPointIso D).hom
          (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)
    let : PreservesFiniteColimits (inverseImageFiniteModules l E (frobeniusPointIso D).hom n) := by
      with_unfolding_all
        exact isoSectionwiseModuleInverseImage_colimits (frobeniusPointIso D).hom
          (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)
    have hc : finiteKappa D l hl E n (finiteComplex D l E n M) ≫
        (finiteLambda D l E n (finiteComplex D l E n M) e).hom = 𝟙 _ := by
      let K := finiteComplex D l E n M
      let A :=
        (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.app
        K
      let B :=
        (integralOperationsLevelPullback l E
          (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.app K
      let : (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
          (CommRingCat.of (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
        integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n
      let : PreservesFiniteLimits (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
        inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom n
      let : PreservesFiniteColimits (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
        inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom n
      let C := (Functor.mapDerivedCategoryNatIso
        (inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
          (Padic.coefficientExtensionRing l E (n + 1)))).app (DerivedCategory.Q.obj K)
      change ((A.hom ≫ DerivedCategory.Q.map
        (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n K) ≫
        B.inv) ≫ C.hom) ≫ (C.symm ≪≫ B ≪≫ DerivedCategory.Q.mapIso e ≪≫ A.symm).hom = _
      have hk : DerivedCategory.Q.map
          (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n K) =
          (DerivedCategory.Q.mapIso e).inv := congrArg DerivedCategory.Q.map hinv
      rw [hk]
      exact isoCancellation A B.symm C (DerivedCategory.Q.mapIso e)
    refine ⟨e, hmul, hinv, hc, hexFin n _, ?_⟩
    intro v
    exact transportCompose
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory)
      _ _ _ _ _ (hrecipeFin n (finiteComplex D l E n M)) hc
  · intro M hM _
    obtain ⟨θ, ε, hε, hθ⟩ := integralComparison D l hl E ⟨_, hM⟩
    have hc : inverseImagePullbackComparisonDerived l E (frobeniusPointIso D).hom
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl)
        (DerivedCategory.Q.obj (integralComplex D l E M)) ≫
        (integralLambda D l E _ θ ε).hom = 𝟙 _ := by
      change _ ≫ θ.hom ≫
        ((inverseImageIntegralDerived l E (frobeniusPointIso D).hom).mapIso ε).inv = _
      rw [← Category.assoc, hθ]
      exact (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).mapIso ε
        |>.hom_inv_id
    refine ⟨θ, ε, quotientNormalization D l hl E M, hε, hθ, hc,
      (hexInt ⟨_, hM⟩).1, ?_⟩
    intro v
    have hv : integralOrdinary D l hl E ⟨_, hM⟩ ≫
        (pointFibreIntegralAmbient D l E).map
          ((integralLambda D l E _ θ ε).hom ≫ (integralSheafIso D l E M v).hom) =
        frobeniusPointIntegralSigmaDerived D l E
          (DerivedCategory.Q.obj (integralComplex D l E M)) ≫
          (pointFibreIntegralAmbient D l E).map (integralSheafIso D l E M v).hom := by
      exact transportCompose (pointFibreIntegralAmbient D l E) _ _ _ _ _
        (hexInt ⟨_, hM⟩).2 hc
    have hr := congrArg (rationalExtension l E).map hv
    simp only [Functor.map_comp] at hr
    refine ⟨hv, ?_, ?_⟩
    · simpa only [pointFibreRationalAmbient, rationalExtension, Functor.comp_map,
        Functor.map_comp] using hr
    · intro Ω _ _ _ ι
      simpa only [pointFibreRationalAmbient, rationalExtension, Functor.comp_map,
        Functor.map_comp] using congrArg (closedExtension l E Ω ι).map hr

end WeilConjectures.PointFrobeniusNormalization
