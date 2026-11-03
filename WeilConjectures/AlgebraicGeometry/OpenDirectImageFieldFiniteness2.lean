/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientExchangeEncoding
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
import WeilConjectures.AlgebraicGeometry.Open.OpenDirectImageFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFieldBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Exchange.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-! # Open direct image over a field with finite primary coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-generic-constructibility-of-direct-image-along-an-open-immersion/
sk-cor-geo-open-finiteness/_section.md and sk-cor-geo-open-finiteness.proof.md,
corollary (7.22) and its proof (blueprint: sk-cor-geo-open-finiteness).

Finite discrete coefficients are the continuous condensed ring, pulled back to each
scheme. Bounded constructibility and the ordinary derived operations are the recorded
module-object constructions. Base change uses the actual mate-based exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open FiniteDiscreteOrdinary

private def reflexiveEncodingIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (T : Scheme.{u}) (e : Encoding A T) :
    coefficientEncoding A (Iso.refl (Mon.mk (coefficient A))) T e ≅
      e.fixedDerived.functor := by
  let i : Mod.comap (coefficientMap (𝟙 (coefficient A)) T) ≅ 𝟭 _ :=
    Mod.comapCongr (by
      change (upperStarFromPoint T).map (𝟙 (coefficient A)) = 𝟙 _
      exact (upperStarFromPoint T).map_id _) ≪≫ Mod.comapId _
  exact Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso i ≪≫ Functor.mapDerivedCategoryIdIso _)
      e.fixedDerived.functor ≪≫ Functor.leftUnitor _

private def fixedEncodingPushIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (eX : Encoding A X) (eY : Encoding A Y) :
    CondensedRing.moduleObjectDerivedPushforward (coefficient A) f ⋙
        eY.fixedDerived.functor ≅
      eX.fixedDerived.functor ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor := by
  let F := CondensedRing.lowerStar (coefficient A) f
  let G := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let ET := eY.ordinary.trans eY.fixed
  let EU := eX.ordinary.trans eX.fixed
  have : ET.functor.Additive := inferInstanceAs
    (eY.ordinary.functor ⋙ eY.fixed.functor).Additive
  have : EU.functor.Additive := inferInstanceAs
    (eX.ordinary.functor ⋙ eX.fixed.functor).Additive
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (encodingPushforwardNatIso A Y X f eY eX) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

private def coefficientEncodingPushIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (eX : Encoding A X) (eY : Encoding A Y) :
    CondensedRing.moduleObjectDerivedPushforward (coefficient A) f ⋙
        coefficientEncoding A (Iso.refl (Mon.mk (coefficient A))) Y eY ≅
      coefficientEncoding A (Iso.refl (Mon.mk (coefficient A))) X eX ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor :=
  Functor.isoWhiskerLeft _ (reflexiveEncodingIso A Y eY) ≪≫
    fixedEncodingPushIso A f eX eY ≪≫
    Functor.isoWhiskerRight (reflexiveEncodingIso A X eX).symm _

private theorem exchange_of_etale
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso ((Etale.derivedBaseChangeMap
      (ModuleCat.{u + 1} Λ) sq.toCommSq).app K.obj)) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj K.obj)) := by
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
    (Etale.isIso_unboundedExchange_ι_obj_iff _ sq.toCommSq K).mp h
  have hαβ := comparison_derivedBaseChangeMap Λ sq K
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
      (_root_.DerivedCategory.Plus.ι.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K))) := inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((baseChangeSourceComparisonIso f g Λ).app K)
      ((baseChangeTargetComparisonIso g' f' Λ).app K) hαβ.symm)).1 this

private theorem exchange_eq_finite
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    CondensedRing.moduleObjectDerivedExchange R sq = CondensedRing.finiteProperExchange R sq := by
  unfold CondensedRing.moduleObjectDerivedExchange CondensedRing.finiteProperExchange
  unfold CondensedRing.moduleObjectDerivedPullbackSquareComparison
    CondensedRing.finitePullbackSquare
  rw [CondensedRing.finitePullbackCongr_eqToIso]
  rfl

set_option maxHeartbeats 2400000 in
-- Allow elaboration of the derived equivalence, direct-image and exchange composites.
/-- Open direct image preserves bounded constructibility and commutes with finite-type
base change over the field, with finite primary coefficients.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-generic-constructibility-of-direct-image-along-an-open-immersion/
sk-cor-geo-open-finiteness/_section.md and sk-cor-geo-open-finiteness.proof.md,
corollary (7.22) (blueprint: sk-cor-geo-open-finiteness).

Proof. Finite type over k makes X and Y Noetherian. The normalized coefficient encoding
and finite-model comparison represent K by a bounded constructible etale complex L.
The etale finite-coefficient open-image and base-change assemblies already implement
specialization of generic open finiteness to Spec k, coefficient devissage and finite
truncation. Apply them to L, since ell^r annihilates A and is invertible over k.
The exact-equivalence/right-derived composition comparisons and the qcqs site comparison
identify the direct images. Reflect bounded constructibility through the finite-model
criterion. For every finite-type T, pullback cancellation proves the actual specified
square cartesian. The etale/pro-etale exchange equation conjugates its exchange to the
etale exchange. The normalized coefficient arrow comparison identifies the internal
unit-square-counit exchange, and hence reflects its invertibility. No separatedness of T,
finite Tor amplitude, or replacement of the canonical map is used.
-/
theorem openDirectImage_field_finiteness_and_baseChange_current
    (k : Type u) [Field k]
    (_hbase : Finite k ∨ IsAlgClosed k)
    [Fact (ringChar k).Prime]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ringChar k ≠ ℓ)
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (r : ℕ) (hr : 1 ≤ r) (hA : (ℓ ^ r : A) = 0)
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ aY = aX)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)))
    (hK : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X K) :
    constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) Y
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.continuousCoefficientRingObj A) j).obj K) ∧
      ∀ (T : Over (Spec (.of k))),
        LocallyOfFiniteType T.hom → QuasiCompact T.hom →
        IsIso ((CondensedRing.moduleObjectDerivedExchange
          (Profinite.continuousCoefficientRingObj A)
          (CommSq.mk ((baseChange_morphism_projections
            (Over.homMk j hj : Over.mk aX ⟶ Over.mk aY) T).1.symm))).app K) := by
  classical
  let Λ := ULift.{u + 1} A
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := ⟨⟩
  let E : ∀ Z : Scheme.{u}, Encoding A Z := fun Z ↦
    if h : IsNoetherian Z then
      haveI := h
      (finiteCoefficientModelComparison A Z).choose
    else (encoding_exists A Z).some
  have hE (Z : Scheme.{u}) [IsNoetherian Z] : FiniteCoefficientModelComparison A Z (E Z) := by
    dsimp only [E]
    rw [dif_pos (inferInstance : IsNoetherian Z)]
    exact (finiteCoefficientModelComparison A Z).choose_spec
  let C (Z : Scheme.{u}) := coefficientEncoding A (Iso.refl (Mon.mk (coefficient A))) Z (E Z)
  obtain ⟨L, hL, ⟨eL⟩⟩ := (fixedBoundedCriterion A X (E X) (hE X) K).mp hK
  let Lplus : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨L, hL.1.1⟩
  let eK : (C X).obj K ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L :=
    (reflexiveEncodingIso A X (E X)).app K ≪≫ eL.symm
  have hΛ : (ℓ ^ r : Λ) = 0 := by
    apply (ULift.ringEquiv : Λ ≃+* A).injective
    simpa only [map_pow, map_natCast, map_zero] using hA
  have hchar : IsUnit (ℓ : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓ).isUnit
  have hcoeff : Etale.IsSmoothBaseChangeCoefficients (ℓ ^ r) Λ (Spec (.of k)) := by
    refine ⟨pow_pos (Fact.out : ℓ.Prime).pos r, inferInstance, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hΛ
    · have hpow : IsUnit ((ℓ ^ r : ℕ) : k) := by
        simpa only [Nat.cast_pow] using hchar.pow r
      simpa only [map_natCast] using
        hpow.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hL' : Etale.DerivedCategory.isBoundedConstructible Λ X L := by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hL
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hc q), min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha q
        (hq.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb q
        ((le_max_right _ _).trans_lt hq)
  refine ⟨?_, ?_⟩
  · have hp := Etale.isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion
      k Λ (ℓ ^ r) hcoeff aY j L hL'
    have hp' : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.obj L) := by
      obtain ⟨hc, a, b, _, hv⟩ := hp
      refine ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff _ a).2
        (fun i hi ↦ hv i (Or.inl hi))⟩,
        ⟨b, (_root_.DerivedCategory.isLE_iff _ b).2
          (fun i hi ↦ hv i (Or.inr hi))⟩⟩, fun q ↦ ?_⟩
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
    let epush := (coefficientEncodingPushIso A j (E X) (E Y)).app K ≪≫
      (lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.mapIso eK ≪≫
      ((rightDerivedLowerStarComparisonIso' j (ModuleCat.{u + 1} Λ)).app Lplus).symm ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlusCompatibility.app
          Lplus)
    have hpPro := DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      hp'
    have hpC := (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y).prop_of_iso
      epush.symm hpPro
    apply (fixedBoundedCriterion A Y (E Y) (hE Y) _).mpr
    exact (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y).prop_of_iso
      ((reflexiveEncodingIso A Y (E Y)).app _) hpC
  · intro T hft hqc
    have : LocallyOfFiniteType T.hom := hft
    have : QuasiCompact T.hom := hqc
    let jT := ((Over.pullback T.hom).map
      (Over.homMk j hj : Over.mk aX ⟶ Over.mk aY)).left
    have hY : IsPullback (pullback.fst aY T.hom) (pullback.snd aY T.hom) aY T.hom :=
      IsPullback.of_hasPullback _ _
    have sq : IsPullback (pullback.fst aX T.hom) jT j (pullback.fst aY T.hom) := by
      apply IsPullback.of_bot (v₂₁ := pullback.snd aY T.hom)
        (v₂₂ := aY) _ _ hY
      · have hjT : jT ≫ pullback.snd aY T.hom = pullback.snd aX T.hom :=
          (baseChange_morphism_projections
            (Over.homMk j hj : Over.mk aX ⟶ Over.mk aY) T).2
        rw [hjT, hj]
        exact IsPullback.of_hasPullback aX T.hom
      · exact (baseChange_morphism_projections
          (Over.homMk j hj : Over.mk aX ⟶ Over.mk aY) T).1.symm
    have : QuasiCompact jT := MorphismProperty.of_isPullback sq inferInstance
    have : QuasiSeparated jT := MorphismProperty.of_isPullback sq inferInstance
    have hEt := (Etale.isIso_derivedBaseChangeMap_openImmersion_field_and_isBoundedConstructible
      k ℓ hℓ.symm Λ r hr hΛ aX aY T.hom j hj
      (pullback.fst aX T.hom) (pullback.fst aY T.hom)
      (pullback.snd aY T.hom) jT hY sq L hL').1
    have hPro := exchange_of_etale Λ sq Lplus hEt
    have hC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((C X).obj K)) :=
      (NatTrans.isIso_app_iff_of_iso _ eK).mpr hPro
    let csq : ChosenCartesianSquare (pullback.fst aX T.hom) jT j
        (pullback.fst aY T.hom) :=
      { sq.toCommSq with
        isoPullback := sq.isoPullback
        hom_fst := sq.isoPullback_hom_fst
        hom_snd := sq.isoPullback_hom_snd }
    rw [exchange_eq_finite]
    exact (finiteCoefficientExchangeEncoding_isIso A
      (Iso.refl (Mon.mk (coefficient A))) E csq K).mpr hC


end AlgebraicGeometry.ProEtale
