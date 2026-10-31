/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.Sf.SfConstructibleExceptionalAdjointDischarge
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists

import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite-coefficient smooth purity

Source: Weil conjectures blueprint, main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
thm-pur-finite-coefficient-smooth-purity
(blueprint: thm-pur-finite-coefficient-smooth-purity).

The assertion concerns the specified canonical smooth purity map on the original
small-pro-etale constructible finite-Tor object, at every positive coefficient level.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

private theorem torAmplitude_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro M N he f hf hN F i hi
  exact h.2 M N (he.map (fun eM ↦ eM ≪≫ e.symm)) f hf hN F i hi

-- Retain an actual bounded etale representative and transfer its Tor bound through
-- the canonical realization equivalence. No object used to define purity is chosen here.
private theorem finitePurityPresentation (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    ∃ K₀ : _root_.DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      _root_.DerivedCategory.TStructure.t.plus K₀ ∧
      ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀) ∧
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅
          (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) := by
  classical
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let R := ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring
  have : R.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : PreservesFiniteLimits R :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits Y P.Ring
  have : PreservesFiniteColimits R :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits Y P.Ring
  obtain ⟨a, ha⟩ := hK.1.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.1.bddAbove
  have hz (i : ℤ) (hi : i < min a b ∨ max a b < i) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K) := by
    by_contra hn
    have ha' := ha hn
    have hb' := hb hn
    rcases hi with hi | hi <;> omega
  obtain ⟨J, ⟨eJ⟩⟩ :=
    ((Scheme.finiteRing_constructibleDerived_origin Y P.Ring).2.2.1 K).mpr
      ⟨hK.1.2, min a b, max a b, min_le_max, hz⟩
  let eCJ : E.functor.obj (C.mapDerivedCategory.obj J.obj) ≅ K :=
    ((Functor.mapDerivedCategoryCompIso C R).app J.obj).symm ≪≫ eJ
  let e : C.mapDerivedCategory.obj J.obj ≅ E.inverse.obj K :=
    E.unitIso.app (C.mapDerivedCategory.obj J.obj) ≪≫ E.inverse.mapIso eCJ
  obtain ⟨c, d, hcd, hv⟩ := J.property.2
  have hJ : Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} P.Coefficient) Y J.obj := by
    refine ⟨⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩, fun i ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff J.obj c).mpr fun i hi ↦ hv i (.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff J.obj d).mpr fun i hi ↦ hv i (.inr hi)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (J.property.1 i)
  refine ⟨J.obj, hJ.1.1, ?_, ⟨e⟩⟩
  refine ⟨ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
    hJ, ?_⟩
  obtain ⟨r, s, ht⟩ := hK.2
  have ht' := torAmplitude_of_iso Y P.Ring eCJ.symm r s ht
  exact ⟨r, s, (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    P.Ring Y r s ht.1 (C.mapDerivedCategory.obj J.obj)).mp ht'⟩

private theorem isIso_finitePurityTheta (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K)
    (hplus : _root_.DerivedCategory.TStructure.t.plus K₀)
    (htensor : IsIso ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        (Etale.dualizingComplexTensorMap P.Coefficient f K₀))) :
    IsIso (P.smoothPurityTheta f K K₀ e) := by
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y K₀ hplus
  dsimp only [smoothPurityTheta, smoothPurityEtaleTheta]
  simp only [Functor.map_comp]
  infer_instance

/-- The canonical finite-coefficient smooth purity map is invertible.
Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
thm-pur-finite-coefficient-smooth-purity
(blueprint: thm-pur-finite-coefficient-smooth-purity).

Proof:
1. Transfer intrinsic constructibility and finite Tor amplitude through the canonical
   coefficient realization. Finite-ring constructible comparison supplies a bounded
   etale representative K₀ of the original K.
2. Apply the tensor clause of cohomological smoothness to K₀. The unit of etale/pro-etale
   comparison is invertible on K₀, so all factors of smoothPurityTheta are invertible.
3. Tensoring the inverse normalized diagonal orientation gives an isomorphism.
   The defining uniqueness equation identifies the intrinsic tensor map with the
   composite of this factor and smoothPurityTheta in the chosen presentation.
4. The twist reassociation is an isomorphism. Realization preserves isomorphisms,
   so its composite with the intrinsic tensor map is an isomorphism.
-/
theorem isIso_smoothPurityMap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    IsIso (P.smoothPurityMap f d K hK) := by
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  let : HasCompactification f := inferInstance
  obtain ⟨K₀, hplus, hctf, ⟨e⟩⟩ := finitePurityPresentation P Y K hK
  have htensor := (ProEtale.isCohomologicallySmooth_of_smooth P f d).1.2.1 K₀ hctf
  have := isIso_finitePurityTheta P f
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) K₀ e hplus htensor
  have hpresentation : IsIso (P.smoothPurityTensorMapInPresentation f d
      (Y ↘ Spec (.of P.field.k))
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) K₀ e) := by
    dsimp only [smoothPurityTensorMapInPresentation]
    infer_instance
  have hchosen : IsIso (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose := by
    rw [(P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose_spec K₀ e]
    exact hpresentation
  dsimp only [smoothPurityMap, smoothPurityTensorMap]
  infer_instance

end WeilConjectures.PurityFiniteSetting
