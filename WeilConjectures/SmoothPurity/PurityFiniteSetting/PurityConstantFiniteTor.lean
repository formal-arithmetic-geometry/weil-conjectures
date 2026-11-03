/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.AbelianConstant
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # The finite constant coefficient has finite Tor amplitude -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The actual constant sheaf is bounded constructible of Tor amplitude zero.
Source: affine-line boundary realization, step 2.
Proof: the constant regular module is the tensor unit and hence flat and constructible.
Exact finite coefficient comparison preserves constructibility, cohomological bounds,
and Tor amplitude. The canonical single-functor comparison gives the displayed object.
(blueprint: lem-pur-constant-finite-tor). -/
theorem constant_finiteTor (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.derivedSheaf h Y false)) := by
  let C := comparisonUpperStar (Modules P) Y
  let R := finiteCoefficientIntrinsicRealization Y P.Ring
  let : R.Additive := finiteCoefficientIntrinsicRealization_additive Y P.Ring
  let : PreservesFiniteLimits R :=
    finiteCoefficientIntrinsicRealization_preservesFiniteLimits Y P.Ring
  let : PreservesFiniteColimits R :=
    finiteCoefficientIntrinsicRealization_preservesFiniteColimits Y P.Ring
  let K := (DerivedCategory.singleFunctor (EtSheaves P Y) 0).obj (P.constantEtale Y)
  have hc : Scheme.IsConstructibleSheaf (P.constantEtale Y) :=
    Etale.isConstructibleSheaf_constantSheaf_self P.Coefficient Y
  let := hc
  have hK : Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y K := by
    have hs := Etale.DerivedCategory.boundedConstructible_singleFunctor_obj
      (P.constantEtale Y) 0
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hs.2 i), 0, 0, le_rfl, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · exact DerivedCategory.isZero_of_isLE _ 0 i hi
  let e : (finiteCoefficientIntrinsicDerivedComparison Y P.Ring).obj K ≅
      R.mapDerivedCategory.obj (P.derivedSheaf h Y false) :=
    (Functor.mapDerivedCategoryCompIso C R).app K ≪≫
      R.mapDerivedCategory.mapIso ((C.mapDerivedCategorySingleFunctor 0).app _)
  have hb := ((Scheme.finiteRing_constructibleDerived_origin Y P.Ring).2.2.1
    (R.mapDerivedCategory.obj (P.derivedSheaf h Y false))).1
      ⟨⟨K, hK⟩, ⟨e⟩⟩
  refine ⟨⟨?_, hb.1⟩, 0, 0, ?_⟩
  · apply (Set.finite_Icc (0 : ℤ) 0).subset
    intro q hq
    by_contra hn
    have hq' : q < 0 ∨ 0 < q := by simpa only [Set.mem_Icc, not_and_or, not_le] using hn
    have hzK : IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
      rcases hq' with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 q hi
      · exact DerivedCategory.isZero_of_isLE _ 0 q hi
    have hz := (finiteCoefficientIntrinsicComparison Y P.Ring)
      |>.isZero_homologyFunctor_mapDerivedCategory_obj hzK
    exact hq (hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e).symm)
  · apply (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn P.Ring Y 0 0 le_rfl _).2
    apply (ProEtale.DerivedCategory.torAmplitudeIn (Modules P) Y 0 0).prop_of_iso
      ((C.mapDerivedCategorySingleFunctor 0).app _)
    apply (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
      (Λ := P.Coefficient) 0 0 K).2
    let := Sheaf.monoidalCategory Y.smallEtaleTopology (Modules P)
    exact DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      (ObjectProperty.prop_unit ObjectProperty.flat)

end WeilConjectures.PurityFiniteSetting
