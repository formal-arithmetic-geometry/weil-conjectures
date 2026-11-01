/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MixedBaseChangeOperations
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExchangeEncoding
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-! Constructible inputs and invertible compact-support exchange. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale


private theorem mixedFiniteCtf_iff_good (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (K : proEtaleDerivedCategory T A) :
    spFiniteConstructibleTor T A K ↔ ReductionGood T A K := by
  constructor
  · rintro ⟨⟨a, b, hab, hv⟩, hc, ht⟩
    refine ⟨(Set.finite_Icc a b).subset ?_, hc, ht⟩
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hv i (Or.inl h))),
      le_of_not_gt (fun h ↦ hi (hv i (Or.inr h)))⟩
  · rintro ⟨hb, hc, ht⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (bounded_iff_finite_support K).mpr hb
    refine ⟨⟨min a b, max a b, min_le_max, ?_⟩, hc, ht⟩
    intro i hi
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).mp ha i (hi.trans_le (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).mp hb i ((le_max_right _ _).trans_lt hi)

private def mixedRealizationRestriction (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    proEtaleModuleRestriction T A ⋙ (sfIntrinsicModuleEquivalence T A).functor ≅ 𝟭 _ :=
by
  letI : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    (surjectiveTower_hasSheafify.{u, u} T).isRightAdjoint
  letI : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    surjectiveTower_wEqualsLocallyBijective.{u, u} T
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact intrinsicRealizationRestrictionIso T A _
  · intro M N f
    exact (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (finiteCoefficientIntrinsicScalarMap T A)).counit.naturality f

private def mixedDerivedRestrictionRealizationIso (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (proEtaleDerivedModuleRestriction T A).obj
      ((sfIntrinsicDerivedEquivalence T A).functor.obj K) ≅ K :=
  (sfIntrinsicDerivedEquivalence T A).functor.preimageIso
    (((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (mixedRealizationRestriction T A) ≪≫
      Functor.mapDerivedCategoryIdIso _).app
        ((sfIntrinsicDerivedEquivalence T A).functor.obj K))

private theorem mixedGood_pullback (A : Type u) [CommRing A] [Finite A]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (M : proEtaleDerivedCategory X A)
    (hM : ReductionGood X A M) :
    ReductionGood X' A ((proEtaleConstantRingDerivedPullback A g').obj M) := by
  let Λ := ULift.{u + 1, u} A
  let E := sfIntrinsicDerivedEquivalence X A
  let K := E.inverse.obj M
  have hK := (reductionGood_realization_iff X A K).mp
    (reductionGood_iso (E.counitIso.app M).symm hM)
  have hpull : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X'
      ((upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategory.obj K) := by
    obtain ⟨hbc, a, b, ht⟩ := hK
    exact ⟨hbc.mapDerivedCategory_upperStar g', a, b,
      torAmplitudeIn_mapDerivedCategory_upperStar g' ht⟩
  let e := (openSquareDerivedPullbackModel A g').app M ≪≫
    (mixedDerivedTransport A (upperStar (ModuleCat.{u + 1} Λ) g')).app M
  exact reductionGood_iso e.symm
    ((reductionGood_realization_iff X' A _).mpr hpull)

private theorem mixedGood_openOrigin (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleDerivedCategory X A) (hM : ReductionGood X A M) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z
      ((proEtaleDerivedModuleRestriction Z A).obj
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M)) := by
  let Λ := ULift.{u + 1, u} A
  let E := sfIntrinsicDerivedEquivalence X A
  let K := E.inverse.obj M
  have hK := (reductionGood_realization_iff X A K).mp
    (reductionGood_iso (E.counitIso.app M).symm hM)
  let N := (sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
  let eN : N ≅ (sfIntrinsicDerivedEquivalence Z A).functor.obj (J.obj K) :=
    (mixedDerivedTransport A
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)).app M
  let eR := (proEtaleDerivedModuleRestriction Z A).mapIso eN ≪≫
    mixedDerivedRestrictionRealizationIso Z A (J.obj K)
  exact (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z).prop_of_iso eR.symm
    (plusEtaleOrigin_mapDerivedCategory_openImmersionLowerShriek j hK.1.plusEtaleOrigin)

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction proEtaleAmbientRingedPullbackComparison

private theorem mixedConstantExchange_eq (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    directImageConstantExchange A sq =
      proEtaleAmbientRingedExchange sq
        (proEtaleConstantRing X A) (proEtaleConstantRing Y A)
        (proEtaleConstantRing X' A) (proEtaleConstantRing Y' A)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison g A)
        (proEtaleConstantRingComparison g' A) (proEtaleConstantRingComparison f' A)
        ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f A)).trans
          ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q A) sq.w).trans
            (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm)) := rfl

private theorem mixedReflectsEncodedIso
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.ReflectsIsomorphisms]
    {X Y : C} {U V : D} (a : X ⟶ Y) (b : U ⟶ V)
    (e : Arrow.mk (F.map a) ≅ Arrow.mk b) (hb : IsIso b) : IsIso a := by
  have : IsIso (F.map a) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).2 hb
  exact isIso_of_reflects_iso a F

private theorem mixedProperExchange_isIso (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g) (N : proEtaleDerivedCategory X A)
    (hN : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
      ((proEtaleDerivedModuleRestriction X A).obj N)) :
    IsIso ((directImageConstantExchange A sq).app N) := by
  have hex := isIso_derivedBaseChangeMap_app_of_isProper (ULift.{u + 1, u} A)
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd) _ hN
  obtain ⟨eα⟩ := proEtaleConstantExchange_encoding A sq
    ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f A)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q A) sq.w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm)) N
  rw [mixedConstantExchange_eq]
  exact mixedReflectsEncodedIso (proEtaleDerivedModuleRestriction Y' A) _ _ eα hex

private def mixedProperSquare {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} (cpt : Compactification f) :
    ChosenCartesianSquare (pullback.fst cpt.g g) (pullback.snd cpt.g g) cpt.g g :=
  { w := pullback.condition
    isoPullback := Iso.refl _
    hom_fst := Category.id_comp _
    hom_snd := Category.id_comp _ }

private def mixedCompactMiddle (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (_sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f) : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y' A :=
  (sfIntrinsicExtensionByZero cpt.i A).mapDerivedCategory ⋙
    (proEtaleConstantRingDerivedPullback A (pullback.fst cpt.g g) ⋙
      directImageConstantPush A (pullback.snd cpt.g g))

private def mixedCompactLeft (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f) :
    (sfIntrinsicExtensionByZero cpt.i A).mapDerivedCategory ⋙
        (directImageConstantPush A cpt.g ⋙ proEtaleConstantRingDerivedPullback A g) ⟶
      mixedCompactMiddle A sq cpt :=
  Functor.whiskerLeft (sfIntrinsicExtensionByZero cpt.i A).mapDerivedCategory
    (directImageConstantExchange A (mixedProperSquare cpt))

private def mixedCompactRightIso (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f) :
    mixedCompactMiddle A sq cpt ≅ proEtaleConstantRingDerivedPullback A g' ⋙
      reductionCompactSupport A (mixedPullbackCompactification sq cpt).i
        (mixedPullbackCompactification sq cpt).g :=
  Functor.isoWhiskerRight
    (mixedOpenBaseChangeIso A g' (mixedPullbackCompactification sq cpt).i cpt.i
      (pullback.fst cpt.g g)
      (cpt.isPullback_i_ofIsPullback
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)))
    (directImageConstantPush A (mixedPullbackCompactification sq cpt).g)

private theorem mixedCompactSupportExchange_factors (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f) :
    mixedCompactSupportExchange A sq cpt =
      mixedCompactLeft A sq cpt ≫ (mixedCompactRightIso A sq cpt).hom := rfl

private theorem mixedCompApp_eq
    {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (a : F ⟶ G) (b : G ⟶ H) (M : C) :
    (a ≫ b).app M = a.app M ≫ b.app M := rfl

private theorem mixedCompactSupportExchange_app (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f) (M : proEtaleDerivedCategory X A) :
    (mixedCompactSupportExchange A sq cpt).app M =
      (mixedCompactLeft A sq cpt).app M ≫ (mixedCompactRightIso A sq cpt).hom.app M :=
  (congrArg (fun a ↦ a.app M) (mixedCompactSupportExchange_factors A sq cpt)).trans
    (mixedCompApp_eq _ _ M)

private theorem mixedCompactLeft_eq (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f) :
    mixedCompactLeft A sq cpt =
      Functor.whiskerLeft (sfIntrinsicExtensionByZero cpt.i A).mapDerivedCategory
        (directImageConstantExchange A (mixedProperSquare cpt)) := rfl

private theorem mixedWhiskerLeft_isIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) {F G : D ⥤ E} (a : F ⟶ G) (M : C)
    (ha : IsIso (a.app (J.obj M))) : IsIso ((Functor.whiskerLeft J a).app M) := ha

private theorem mixedIsoApp_of_eq
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (a b : F ⟶ G) (h : a = b) (M : C) (hb : IsIso (b.app M)) :
    IsIso (a.app M) := by
  subst h
  exact hb

private theorem mixedCompactLeft_isIso (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f) (M : proEtaleDerivedCategory X A)
    (hM : ReductionGood X A M) : IsIso ((mixedCompactLeft A sq cpt).app M) := by
  apply mixedIsoApp_of_eq _ _ (mixedCompactLeft_eq A sq cpt) M
  exact mixedWhiskerLeft_isIso (sfIntrinsicExtensionByZero cpt.i A).mapDerivedCategory
    (directImageConstantExchange A (mixedProperSquare cpt)) M
    (mixedProperExchange_isIso A (mixedProperSquare cpt) _
      (mixedGood_openOrigin A cpt.i M hM))

private theorem mixedIsIso_of_hom_eq
    {C : Type*} [Category C] {X Y : C} (a b : X ⟶ Y)
    (h : a = b) (hb : IsIso b) : IsIso a := by
  subst h
  exact hb

private theorem mixedGood_compactExchange (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (cpt : Compactification f) (M : proEtaleDerivedCategory X A)
    (hM : ReductionGood X A M) :
    IsIso ((mixedCompactSupportExchange A sq cpt).app M) := by
  have hleft := mixedCompactLeft_isIso A sq cpt M hM
  have hright := NatIso.hom_app_isIso (mixedCompactRightIso A sq cpt) M
  apply mixedIsIso_of_hom_eq _ _ (mixedCompactSupportExchange_app A sq cpt M)
  infer_instance

set_option linter.unusedVariables false in
/-- Pullback preserves the intrinsic bounded constructible finite-Tor inputs, and the
specified compact-support exchange is invertible on them.
Source: blueprint det-sp-mixed-base-change, Step 4; finite proper base change and
constructible pullback, det-thm-sf-ctf-stability-direct-images clause (1)
(blueprint: lem-sp-mixed-base-change-input).

Proof: finite-type schemes over a field are Noetherian. Pullback of a finite locally
constant stratification is constructible. Exact inverse image preserves cohomological
bounds, and its canonical tensor comparison preserves the same Tor interval. Thus
pullback sends each intrinsic Dctf object to Dctf. For compact-support exchange, choose
its bounded etale antecedent by finite-ring constructible derived origin. Extend this
antecedent by zero along cpt.i, using the exact open-extension comparison. Proper
base change makes the proper exchange at this open extension invertible. The normalized
counit-mate transport identifies that exchange with directImageConstantExchange. The
open factor mixedOpenBaseChangeIso is already an isomorphism by construction. Their
composite is exactly mixedCompactSupportExchange, hence is invertible. This argument
also covers empty schemes and zero coefficient rings, and requires no flatness of a
coefficient change. -/
theorem mixedBaseChange_input
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y X' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (cpt : Compactification f) [cpt.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (cpt.Z ↘ Spec (.of k))]
    [QuasiCompact (cpt.Z ↘ Spec (.of k))] [IsSeparated (cpt.Z ↘ Spec (.of k))]
    [cpt.i.IsOver (Spec (.of k))] [cpt.g.IsOver (Spec (.of k))]
    {Y' : Scheme.{u}} [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare g' f' f g)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (M : proEtaleDerivedCategory X A) (hM : spFiniteConstructibleTor X A M) :
    spFiniteConstructibleTor X' A
        ((proEtaleConstantRingDerivedPullback A g').obj M) ∧
      IsIso ((mixedCompactSupportExchange A sq cpt).app M) := by
  have hgood := (mixedFiniteCtf_iff_good X A M).mp hM
  refine ⟨(mixedFiniteCtf_iff_good X' A _).mpr (mixedGood_pullback A g' M hgood), ?_⟩
  exact mixedGood_compactExchange A sq cpt M hgood

end AlgebraicGeometry.ProEtale
