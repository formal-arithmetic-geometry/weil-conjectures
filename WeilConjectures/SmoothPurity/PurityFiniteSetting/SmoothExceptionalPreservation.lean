/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleIntervals
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicComparisonConstructibility

/-! # Smooth exceptional inverse image preserves the two finite coefficient classes

Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
cor-pur-smooth-admissibility, order 2077 (blueprint: cor-pur-smooth-admissibility).

These are the two preservation clauses, with signed shift -2d. The unrestricted
ambient adjoint datum is not a hypothesis or a conclusion. No assertion at integral,
rational, or algebraically closed coefficients is made.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The coefficient prime is invertible in every local ring of every k-scheme.
Source: the fixed setting of cor-pur-smooth-admissibility, proof step 1
(blueprint: cor-pur-smooth-admissibility).
Proof: the finite field has cardinality p^a, hence characteristic p; its algebraic
closure has characteristic p as well. Since ell differs from p, ell is nonzero
and therefore a unit in k. Its image under the structure map to each local ring
is a unit. No smoothness or finite-type assumption is needed for this observation. -/
theorem prime_isUnit_stalk (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (t : T) :
    IsUnit (P.coefficients.l : T.presheaf.stalk t) := by
  exact P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)) t

private instance coefficient_finite (P : PurityFiniteSetting.{u}) [Finite P.Ring] :
    Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

private theorem coefficient_power_zero (P : PurityFiniteSetting.{u}) :
    ((P.coefficients.l ^ P.level : ℕ) : P.Ring) = 0 := by
  let l := P.coefficients.l
  let E := P.extension
  let n := P.level
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  change ((l ^ n : ℕ) :
    Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
  rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
    Ideal.Quotient.eq_zero_iff_mem]
  simpa only [Nat.cast_pow] using hpow

private theorem coefficient_invertibleExponent (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] :
    HasInvertibleExponent P.Coefficient T := by
  refine ⟨P.coefficients.l ^ P.level, pow_pos (Fact.out : P.coefficients.l.Prime).pos _,
    ?_, ?_⟩
  · apply ULift.ext
    exact coefficient_power_zero P
  · apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro t ht
    change IsUnit ((T.toRingedSpace.presheaf.germ ⊤ t ht).hom
      ((P.coefficients.l ^ P.level : ℕ) : T.toRingedSpace.presheaf.obj _))
    rw [map_natCast, Nat.cast_pow]
    exact (P.prime_isUnit_stalk T t).pow P.level

private noncomputable instance restriction_additive (T : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B] : (proEtaleModuleRestriction T B).Additive where
  map_add := by intros; rfl

private noncomputable instance restriction_equivalence (T : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B] :
    (proEtaleModuleRestriction T B).IsEquivalence :=
  proEtaleModuleRestriction_isEquivalence T B

private theorem intrinsic_fixed_bounded (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (K : proEtaleDerivedCategory T P.Ring)
    (hK : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
      P.level_pos T K) [Finite P.Ring] :
    _root_.DerivedCategory.TStructure.t.bounded
      ((proEtaleModuleRestriction T P.Ring).mapDerivedCategory.obj K) := by
  obtain ⟨a, ha⟩ := hK.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.bddAbove
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := by
    by_contra hn
    rcases hq with hq | hq
    · exact (not_le_of_gt hq) (ha hn)
    · exact (not_le_of_gt hq) (hb hn)
  exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr (fun q hq ↦
    (proEtaleModuleRestriction T P.Ring).isZero_homologyFunctor_mapDerivedCategory_obj
      (hz q (Or.inl hq)))⟩,
    ⟨b, (_root_.DerivedCategory.isLE_iff _ b).mpr (fun q hq ↦
    (proEtaleModuleRestriction T P.Ring).isZero_homologyFunctor_mapDerivedCategory_obj
      (hz q (Or.inr hq)))⟩⟩

private theorem intrinsic_fixed_origin (P : WeilConjectures.PurityFiniteSetting.{u})
    [Finite P.Ring]
    (T : Scheme.{u}) (K : proEtaleDerivedCategory T P.Ring)
    (hK : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
      P.level_pos T K) :
    ∃ G : Etale.DerivedCategoryModule P.Coefficient T,
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient T G ∧
      Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        T).mapDerivedCategory.obj G ≅
          (proEtaleModuleRestriction T P.Ring).mapDerivedCategory.obj K) := by
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
  let R := proEtaleModuleRestriction T P.Ring
  have : R.IsEquivalence := proEtaleModuleRestriction_isEquivalence T P.Ring
  let M := R.mapDerivedCategory.obj K
  have hc (q : ℤ) : ProEtale.IsConstructible P.Coefficient
      ((_root_.DerivedCategory.homologyFunctor _ q).obj M) := by
    exact ProEtale.isConstructible_of_iso ((R.mapDerivedCategoryHomologyFunctorIso q).app K)
      ((proEtaleModuleRestriction_constructible_iff T P.Ring _).mp (hK.2 q))
  have : IsIso (ProEtale.derivedComparisonAdjunctionPlus
      (ModuleCat.{u + 1} P.Coefficient) T).unit :=
    ProEtale.isIso_compactSupportComparisonUnit T P.Coefficient
  have : ν.mapDerivedCategoryPlus.Full :=
    (ProEtale.derivedComparisonAdjunctionPlus
      (ModuleCat.{u + 1} P.Coefficient) T).fullyFaithfulLOfIsIsoUnit.full
  let F := ν.mapDerivedCategoryPlus ⋙ _root_.DerivedCategory.Plus.ι
  have hsingle (G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
      (hG : ν.essImage G) : F.essImage ((_root_.DerivedCategory.singleFunctor _ 0).obj G) := by
    obtain ⟨H, ⟨e⟩⟩ := hG
    exact ⟨(_root_.DerivedCategory.Plus.singleFunctor _ 0).obj H,
      ⟨ν.mapDerivedCategoryPlusCompatibility.app _ ≪≫
        ν.mapDerivedCategory.mapIso ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).app H) ≪≫
        (ν.mapDerivedCategorySingleFunctor 0).app H ≪≫
        (_root_.DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩
  have hM : F.essImage M := _root_.DerivedCategory.prop_of_bounded F.essImage
    ν.essImage hsingle M (intrinsic_fixed_bounded P T K hK) (fun q ↦ by
      obtain ⟨G, _, he⟩ := ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
        P.Coefficient (hc q)
      exact ⟨G, he⟩)
  obtain ⟨G, ⟨e⟩⟩ := hM
  let e' : ν.mapDerivedCategory.obj G.obj ≅ M :=
    (ν.mapDerivedCategoryPlusCompatibility.app G).symm ≪≫ e
  refine ⟨G.obj, ⟨?_, ?_⟩, ⟨e'⟩⟩
  · intro q
    have hq := ProEtale.isConstructible_of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e'.symm) (hc q)
    have hν := ProEtale.isConstructible_of_iso
      ((ν.mapDerivedCategoryHomologyFunctorIso q).symm.app G.obj) hq
    obtain ⟨H, hH, ⟨eH⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj P.Coefficient hν
    have : Scheme.IsConstructibleSheaf H := hH
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.of_iso (ν.preimageIso eH))
  · obtain ⟨a, b, hab⟩ :=
      (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded M).mpr
        (intrinsic_fixed_bounded P T K hK)
    refine ⟨min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    apply ν.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    apply IsZero.of_iso _ ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e')
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff M a).mp hab.1 q
        (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff M b).mp hab.2 q hq

private noncomputable def comparison_restriction_iso (P : PurityFiniteSetting.{u})
    [Finite P.Ring] (T : Scheme.{u}) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison T P.Ring) ⋙
      (proEtaleModuleRestriction T P.Ring).mapDerivedCategory ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory := by
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
  let E := ProEtale.finiteCoefficientIntrinsicRealization T P.Ring
  let R := proEtaleModuleRestriction T P.Ring
  have : ν.Additive := inferInstanceAs
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).Additive
  have : E.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive T P.Ring
  have : R.Additive := restriction_additive T P.Ring
  have : PreservesFiniteLimits ν := inferInstanceAs
    (PreservesFiniteLimits (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) T))
  have : PreservesFiniteColimits ν := inferInstanceAs
    (PreservesFiniteColimits (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) T))
  have : PreservesFiniteLimits E :=
    (ProEtale.finiteCoefficientIntrinsicRealization_exact T P.Ring).2.2.1
  have : PreservesFiniteColimits E :=
    (ProEtale.finiteCoefficientIntrinsicRealization_exact T P.Ring).2.2.2
  have : R.IsEquivalence := proEtaleModuleRestriction_isEquivalence T P.Ring
  let e := (ProEtale.intrinsicRealization_restriction T P.Ring).some
  exact (Functor.mapDerivedCategoryCompIso (ν ⋙ E) R).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Functor.associator ν E R) ≪≫ Functor.isoWhiskerLeft ν e ≪≫ Functor.rightUnitor ν)

private theorem intrinsic_origin (P : PurityFiniteSetting.{u}) [Finite P.Ring]
    (T : Scheme.{u}) (K : proEtaleDerivedCategory T P.Ring)
    (hK : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
      P.level_pos T K) :
    ∃ G : Etale.DerivedCategoryModule P.Coefficient T,
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient T G ∧
      Nonempty (K ≅ (ProEtale.finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj G) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := intrinsic_fixed_origin P T K hK
  refine ⟨G, hG, ⟨?_⟩⟩
  exact ((proEtaleModuleRestriction T P.Ring).mapDerivedCategory.preimageIso
    ((comparison_restriction_iso P T).app G ≪≫ e)).symm

private noncomputable def exceptional_origin_iso (P : PurityFiniteSetting.{u})
    [Finite P.Ring] (X Y : Scheme.{u})
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (G : Etale.DerivedCategoryModule P.Coefficient Y)
    (hG : _root_.DerivedCategory.TStructure.t.plus G)
    (K : proEtaleDerivedCategory Y P.Ring)
    (e : K ≅ (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y P.Ring).obj G) :
    (finiteExceptionalInverseImage P.coefficients.l P.extension P.level P.level_pos
      P.field.k X Y f).obj K ≅
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj
        ((Etale.rightDerivedUpperShriek P.Coefficient f).obj G) := by
  let E := ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring
  have : E.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact
    Y P.Ring).1
  have : E.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : E.asEquivalence.functor.Additive :=
    ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : E.asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let Rν := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let F := Etale.rightDerivedUpperShriek P.Coefficient f
  let C := ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring
  let e₁ : E.asEquivalence.inverse.mapDerivedCategory.obj K ≅
      ν.mapDerivedCategory.obj G :=
    E.asEquivalence.inverse.mapDerivedCategory.mapIso e ≪≫
    E.asEquivalence.inverse.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryCompIso ν E).app G) ≪≫
    E.asEquivalence.mapDerivedCategory.unitIso.symm.app _
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y G hG
  let e₂ : Rν.obj (ν.mapDerivedCategory.obj G) ≅ G :=
    (asIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} P.Coefficient) Y).unit.app G)).symm
  exact C.mapIso (F.mapIso (Rν.mapIso e₁ ≪≫ e₂))

private theorem recorded_bounded_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (G : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T G ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T G := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff G a).mpr
      (fun q hq ↦ hz q (Or.inl hq))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff G b).mpr
        (fun q hq ↦ hz q (Or.inr hq))⟩⟩, fun q ↦ ?_⟩
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc q)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc q),
      min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff G a).mp ha q
        (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff G b).mp hb q hq

private theorem smooth_etale_interval (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [HasInvertibleExponent A Y]
    (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (a b : ℤ) (G : Etale.DerivedCategoryModule A Y)
    (hG : _root_.DerivedCategory.homologyConcentratedIn a b G) :
    _root_.DerivedCategory.homologyConcentratedIn (a - 2 * d) (b - 2 * d)
      ((Etale.rightDerivedUpperShriek A f).obj G) := by
  let := Etale.derivedBraidedCategory A X
  have : HasInvertibleExponent A X := .of_hom f
  obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := Etale.exists_dualizingComplex_iso_and_tensor A f d
  obtain ⟨et⟩ := Etale.nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex
    A f d G
  obtain ⟨_, hLf⟩ := Etale.isConstructibleSheaf_and_flat_of_sheafFiber_iso A L hLs
  have hp := (Etale.upperStar (ModuleCat.{u + 1} A) f)
    |>.homologyConcentratedIn_mapDerivedCategory_obj hG
  have hp' : _root_.DerivedCategory.homologyConcentratedIn a b
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj G) :=
    (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      ((Etale.upperStar (ModuleCat.{u + 1} A) f)
        |>.leftDerivedFunctorIsoMapDerivedCategory.app G).symm hp
  have hL₀ := Etale.torAmplitudeIn_singleFunctor_zero_of_flat (ModuleCat A) L hLf
  have ht := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right
    hp' hL₀
  simp only [add_zero] at ht
  let e := et.symm ≪≫
    ((Etale.derivedTensor (ModuleCat A) X).obj _).mapIso eω ≪≫
    ((((Etale.derivedTensor (ModuleCat A) X).obj _).commShiftIso (2 * d : ℤ)).app _)
  obtain ⟨h₁, h₂⟩ := ht
  let M := ((Etale.derivedTensor (ModuleCat A) X).obj
    ((Etale.upperStar (ModuleCat A) f).leftDerivedFunctor.obj G)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L)
  have : _root_.DerivedCategory.TStructure.t.IsGE M a := h₁
  have : _root_.DerivedCategory.TStructure.t.IsLE M b := h₂
  have hs : _root_.DerivedCategory.homologyConcentratedIn (a - 2 * d) (b - 2 * d)
      (M⟦(2 * d : ℤ)⟧) :=
    ⟨_root_.DerivedCategory.TStructure.t.isGE_shift M a (2 * d : ℤ) (a - 2 * d),
      _root_.DerivedCategory.TStructure.t.isLE_shift M b (2 * d : ℤ) (b - 2 * d)⟩
  exact (_root_.DerivedCategory.homologyConcentratedIn _ _).prop_of_iso e.symm hs

private noncomputable instance comparison_faithful (P : PurityFiniteSetting.{u})
    [Finite P.Ring] (T : Scheme.{u}) :
    (ProEtale.finiteCoefficientIntrinsicComparison T P.Ring).Faithful := by
  have := (ProEtale.finiteCoefficientIntrinsicRealization_exact T P.Ring).1
  change (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T ⋙
    ProEtale.finiteCoefficientIntrinsicRealization T P.Ring).Faithful
  infer_instance

private theorem intrinsic_of_iso (P : PurityFiniteSetting.{u}) [Finite P.Ring]
    (T : Scheme.{u}) {K L : proEtaleDerivedCategory T P.Ring} (e : K ≅ L)
    (hL : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
      P.level_pos T L) :
    intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
      P.level_pos T K := by
  constructor
  · apply hL.1.subset
    intro i hi hz
    exact hi (hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e))
  · intro i
    apply (proEtaleModuleRestriction_constructible_iff T P.Ring _).mpr
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T P.Ring).mapIso
        ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e)).symm
      ((proEtaleModuleRestriction_constructible_iff T P.Ring _).mp (hL.2 i))

private theorem tor_of_iso (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) {K L : proEtaleDerivedCategory T P.Ring} (e : K ≅ L)
    {a b : ℤ} (hL : HasProEtaleTorAmplitude T P.Ring L a b) :
    HasProEtaleTorAmplitude T P.Ring K a b := by
  refine ⟨hL.1, ?_⟩
  intro Q R he g hg hR M i hi
  exact hL.2 Q R (he.map (fun z ↦ z ≪≫ e)) g hg hR M i hi

private noncomputable instance residue_invertible (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] :
    ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
  (show IsUnit (P.coefficients.l : T.residueField x) by
    simpa only [map_natCast] using
      (P.prime_isUnit_stalk T x).map (IsLocalRing.residue (T.presheaf.stalk x))).invertible

private theorem concentrated_of_interval (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (a b : ℤ) (hab : a ≤ b)
    (K : proEtaleDerivedCategory T P.Ring)
    (hK : finiteTorsionConstructibleIn P.coefficients.l P.extension P.level
      P.level_pos T (P.prime_isUnit_stalk T) a b hab K) :
    _root_.DerivedCategory.homologyConcentratedIn a b K := by
  refine ⟨(_root_.DerivedCategory.isGE_iff K a).mpr (fun q hq ↦ ?_),
    (_root_.DerivedCategory.isLE_iff K b).mpr (fun q hq ↦ ?_)⟩
  · exact hK.2 q (fun h ↦ (not_le_of_gt hq) h.1)
  · exact hK.2 q (fun h ↦ (not_le_of_gt hq) h.2)

private theorem interval_of_concentrated (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (a b : ℤ) (hab : a ≤ b)
    (K : proEtaleDerivedCategory T P.Ring)
    (hK : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
      P.level_pos T K)
    (hc : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    finiteTorsionConstructibleIn P.coefficients.l P.extension P.level
      P.level_pos T (P.prime_isUnit_stalk T) a b hab K := by
  refine ⟨hK, fun q hq ↦ ?_⟩
  have hq' : q < a ∨ b < q := by simpa only [Set.mem_Icc, not_and_or, not_le] using hq
  rcases hq' with hq' | hq'
  · exact (_root_.DerivedCategory.isGE_iff K a).mp hc.1 q hq'
  · exact (_root_.DerivedCategory.isLE_iff K b).mp hc.2 q hq'

/-- Smooth separated finite-type morphisms of finite-type k-schemes shift both
constructible cohomological intervals and finite Tor amplitude by -2d. The first
clause quantifies over all bounded constructible inputs, including those of infinite
Tor dimension. The final clause explicitly gives preservation of D^b_ctf.
Source: blueprint cor-pur-smooth-admissibility, clauses (1)--(2), order 2077
(blueprint: cor-pur-smooth-admissibility).

Proof, following the eight steps of the node:
1. Finite type over k makes X and Y Noetherian and Y qcqs. Nagata gives a
compactification of f. The coefficient ring is finite, and ell^n annihilates it,
since ell belongs to the uniformizer ideal. This exponent is invertible on Y.
Apply thm-asd-smooth-tensor with precisely these hypotheses.
2. By lem-sf-proetale-constructible-origin, choose an etale representative G of
any bounded constructible input M. Exact comparison identifies its cohomology
with that of M, and reflects zero sheaves. Thus G has the same interval as M.
The defining exceptional functor formula gives nu_X^* f^times G. The adjunction
interpretation is cor-sf-ambient-adjoint-discharge, without an ambient hypothesis.
3. Smooth tensor duality identifies f^times G with f^*G tensor omega_f for every
G, and omega_f with T[2d] for a locally constant free rank-one module sheaf T.
Choose an etale cover trivializing T; no Tate orientation is necessary.
4. Monoidal inverse image and the triangulatedness of derived tensor identify
these local restrictions with (u^* f^*G)[2d]. The final tensor unit is computed
on a K-flat representative P by P tensor A = P.
5. Exact inverse image gives H^r locally equal to u^* f^* H^(r+2d)(G).
It vanishes outside [a-2d,b-2d]. Pull back the finite constructible
stratification of each cohomology sheaf; on every stratum, refine the trivializing
cover by a cover on which the pulled-back sheaf is finite constant. This proves
constructibility with the same finite strata, even if the cover is infinite.
Comparison gives clause (1), with no assumption about Tor amplitude.
6. For K of finite Tor amplitude, lem-sf-comparison-tor-amplitude reflects
its interval to its bounded constructible etale representative G. The residue
criterion lem-exc-residue-tor-test says G tensor kappa has that interval.
7. On the same trivializing cover, the residue tensor of H = f^times G is
(u^* f^*(G tensor kappa))[2d]. Exact inverse image and the cohomology shift
put it in [a-2d,b-2d]. Coverwise vanishing is vanishing of the sheaf.
8. H is already bounded constructible by step 5. The etale residue test now
proves its shifted Tor interval; comparison preserves this interval against all
pro-etale degree-zero module sheaves. Bounded constructibility and finite Tor
amplitude give D^b_ctf preservation. These are exactly the signed constants
c_f^- = c_f^+ = -2d; coefficient transport at other stages is not asserted. -/
theorem smooth_exceptional_preservation (P : WeilConjectures.PurityFiniteSetting.{u})
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    (∀ (a b : ℤ) (hab : a ≤ b) (L : proEtaleDerivedCategory Y P.Ring),
      finiteTorsionConstructibleIn P.coefficients.l P.extension P.level P.level_pos
        Y (P.prime_isUnit_stalk Y) a b hab L →
      finiteTorsionConstructibleIn P.coefficients.l P.extension P.level P.level_pos
        X (P.prime_isUnit_stalk X) (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ))
        (sub_le_sub_right hab _) ((finiteExceptionalInverseImage P.coefficients.l
          P.extension P.level P.level_pos P.field.k X Y f).obj L)) ∧
    (∀ (a b : ℤ) (K : proEtaleDerivedCategory Y P.Ring),
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K →
      HasProEtaleTorAmplitude Y P.Ring K a b →
      HasProEtaleTorAmplitude X P.Ring
        ((finiteExceptionalInverseImage P.coefficients.l P.extension P.level P.level_pos
          P.field.k X Y f).obj K) (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ))) ∧
    (∀ K : proEtaleDerivedCategory Y P.Ring,
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K →
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X
        ((finiteExceptionalInverseImage P.coefficients.l P.extension P.level P.level_pos
          P.field.k X Y f).obj K)) := by
  -- Use the source library's unoriented smooth purity theorem. Its rank-one line is
  -- flat, so the cohomological interval argument applies without finite Tor amplitude.
  have : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  have : HasCompactification f :=
    hasCompactification_of_finiteType_over_field P.field.k X Y f
  have : HasInvertibleExponent P.Coefficient Y :=
    coefficient_invertibleExponent P Y
  let F := finiteExceptionalInverseImage P.coefficients.l P.extension P.level
    P.level_pos P.field.k X Y f
  have hbounded (K : proEtaleDerivedCategory Y P.Ring)
      (hK : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
        P.level_pos Y K) :
      intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
        P.level_pos X (F.obj K) := by
    obtain ⟨G, hG, ⟨e⟩⟩ := intrinsic_origin P Y K hK
    have hbG := (recorded_bounded_iff P.Coefficient Y G).mp hG
    let eF := exceptional_origin_iso P X Y f G hbG.1.1 K e
    apply intrinsic_of_iso P X eF
    exact intrinsicComparison_boundedConstructible P.field P.coefficients.l
      P.coefficients.different P.extension P.level P.level_pos X _
      ((recorded_bounded_iff P.Coefficient X _).mpr
        (Etale.boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension
          P.Coefficient f d hbG))
  have htor (a b : ℤ) (K : proEtaleDerivedCategory Y P.Ring)
      (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
      (ht : HasProEtaleTorAmplitude Y P.Ring K a b) :
      HasProEtaleTorAmplitude X P.Ring (F.obj K) (a - 2 * d) (b - 2 * d) := by
    obtain ⟨G, hG, ⟨e⟩⟩ := intrinsic_origin P Y K hK.1
    have hbG := (recorded_bounded_iff P.Coefficient Y G).mp hG
    have htG := finiteCoefficient_comparison_reflects_torAmplitude P.field P.coefficients.l
      P.coefficients.different P.extension P.level P.level_pos Y a b G hbG.1.1 K hK.1 ht e
    have htG' := Etale.torAmplitudeIn_of_hasTorAmplitudeIn P.Coefficient htG
    have hout :=
      Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
      P.Coefficient f d a b ⟨⟨hbG,
        _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn htG'⟩, htG'⟩
    have hbc := (recorded_bounded_iff P.Coefficient X _).mpr hout.1.1
    have hcomp := finiteCoefficient_comparison_preserves_torAmplitude P.field P.coefficients.l
      P.coefficients.different P.extension P.level P.level_pos X (a - 2 * d) (b - 2 * d)
      (sub_le_sub_right ht.1 _) _ hbc
      (Etale.hasTorAmplitudeIn_of_torAmplitudeIn hout.2)
    exact tor_of_iso P X (exceptional_origin_iso P X Y f G hbG.1.1 K e) hcomp.2
  refine ⟨?_, htor, ?_⟩
  · intro a b hab K hK
    obtain ⟨G, hG, ⟨e⟩⟩ := intrinsic_origin P Y K hK.1
    have hbG := (recorded_bounded_iff P.Coefficient Y G).mp hG
    let C := ProEtale.finiteCoefficientIntrinsicComparison Y P.Ring
    have hcK := concentrated_of_interval P Y a b hab K hK
    have hcG : _root_.DerivedCategory.homologyConcentratedIn a b G :=
      C.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
        ((_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso e hcK)
    have hcH := smooth_etale_interval P.Coefficient f d a b G hcG
    have hcC := (ProEtale.finiteCoefficientIntrinsicComparison X P.Ring)
      |>.homologyConcentratedIn_mapDerivedCategory_obj hcH
    let eF := exceptional_origin_iso P X Y f G hbG.1.1 K e
    exact interval_of_concentrated P X _ _ (sub_le_sub_right hab _) (F.obj K)
      (hbounded K hK.1)
      ((_root_.DerivedCategory.homologyConcentratedIn _ _).prop_of_iso eF.symm hcC)
  · intro K hK
    obtain ⟨a, b, ht⟩ := hK.2
    exact ⟨hbounded K hK.1, a - 2 * d, b - 2 * d, htor a b K hK ht⟩

end WeilConjectures.PurityFiniteSetting
