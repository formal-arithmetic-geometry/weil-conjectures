/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction
import Sheaf.Paper.EtaleHomFiniteTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Source-etale locality of cohomological smoothness

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality (blueprint: lem-pur-co-smooth-etale-locality).

The two statements give descent from a surjective etale source cover and the
cohomological smoothness and untwisted dualizing object of every etale map in the setting.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem comparison_reflects_iso
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : K ⟶ L)
    (ha : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a)) :
    IsIso a := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  let F := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  have := ha
  have h := (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) a).2
    (show IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
      (F.mapDerivedCategory.map a)) from Functor.map_isIso _ _)
  change IsIso (F.map ((_root_.DerivedCategory.homologyFunctor _ n).map a)) at h
  have := h
  exact isIso_of_reflects_iso _ F

private theorem comparison_lift_iso
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (e : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj K ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L) :
    Nonempty (K ≅ L) := by
  obtain ⟨a, ha⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map K L hL).2 e.hom
  have h : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a) := by
    dsimp only at ha
    rw [ha]
    infer_instance
  have := comparison_reflects_iso Λ X a h
  exact ⟨asIso a⟩

private theorem comparison_reflects_ctf
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj K)) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K := by
  obtain ⟨⟨G, hG, ⟨e⟩⟩, a, b, ht⟩ := h
  obtain ⟨d⟩ := comparison_lift_iso Λ X K G hG.1.1 e.symm
  exact ⟨(Etale.DerivedCategory.boundedConstructible _ X).prop_of_iso d.symm hG,
    a, b, DerivedCategory.torAmplitudeIn_of_mapDerivedCategory Λ ht⟩

private theorem bounded_constructible_coordinates
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule Λ X) :
    Etale.DerivedCategory.isBoundedConstructible Λ X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (.inl hi))
    · exact (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi

private theorem finite_hom_ctf
    (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (K M : Etale.DerivedCategoryModule P.Coefficient X)
    (hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) X K)
    (hM : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) X M) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) X
      (((Etale.derivedHom (ModuleCat.{u + 1} P.Coefficient) X).obj (Opposite.op K)).obj M) := by
  obtain ⟨a₀, b₀, hKt⟩ := hK.2
  obtain ⟨c₀, d₀, hMt⟩ := hM.2
  let a := min a₀ b₀
  let b := max a₀ b₀
  let c := min c₀ d₀
  let d := max c₀ d₀
  have hab : a ≤ b := min_le_max
  have hcd : c ≤ d := min_le_max
  have hKa := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (hKt.mono (min_le_left a₀ b₀) (le_max_right a₀ b₀))
  have hMa := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (hMt.mono (min_le_left c₀ d₀) (le_max_right c₀ d₀))
  obtain ⟨m, hm⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of P.field.k))
  have h := WeilConjectures.finiteCoefficient_derivedHom_ctf_etale
    P.field P.coefficients.l P.coefficients.different P.extension P.level P.level_pos
    X m hm a b c d hab hcd K M
    ⟨(bounded_constructible_coordinates _ X K).2 hK.1, a, b, hab, hKa⟩
    ⟨(bounded_constructible_coordinates _ X M).2 hM.1, c, d, hcd, hMa⟩ hKa hMa
  exact ⟨(bounded_constructible_coordinates _ X _).1 h.1.1, _, _,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 h.2.1⟩

private theorem comparison_invertible
    (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (h : comparedInvertibilityClause P X
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj W)) :
    Etale.DerivedCategory.isInvertible P.Coefficient X W := by
  obtain ⟨N, hN, ⟨e₁⟩, ⟨e₂⟩⟩ := h
  obtain ⟨N', _, ⟨a⟩⟩ := hN.1
  let η := DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso P.Coefficient X
  have hu := (Etale.constructibleFiniteTor_tensorUnit P.Coefficient X).1.1.1
  refine ⟨N', ?_, ?_⟩
  · exact comparison_lift_iso P.Coefficient X _ _ hu
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso _ W).app N' ≪≫
        ((derivedTensor _ X).obj _).mapIso a ≪≫ e₁ ≪≫ η.symm)
  · exact comparison_lift_iso P.Coefficient X _ _ hu
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso _ N').app W ≪≫
        ((derivedTensor _ X).mapIso a).app _ ≪≫ e₂ ≪≫ η.symm)

universe uA

private theorem inverse_hom
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : ∃ N, Nonempty (((Etale.derivedTensor A X).obj W).obj N ≅ 𝟙_ _) ∧
      Nonempty (((Etale.derivedTensor A X).obj N).obj W ≅ 𝟙_ _)) :
    Nonempty (((Etale.derivedTensor A X).obj W).obj
      (((Etale.derivedHom A X).obj (Opposite.op W)).obj (𝟙_ _)) ≅ 𝟙_ _) ∧
    Nonempty (((Etale.derivedTensor A X).obj
      (((Etale.derivedHom A X).obj (Opposite.op W)).obj (𝟙_ _))).obj W ≅ 𝟙_ _) := by
  obtain ⟨N, ⟨e₁⟩, ⟨e₂⟩⟩ := h
  let := exactPairingOfTensorIso e₂ e₁
  let a := MonoidalClosed.ihomObjUnitIso N W
  exact ⟨⟨(whiskerLeftIso W a) ≪≫ e₁⟩, ⟨whiskerRightIso a W ≪≫ e₂⟩⟩

private noncomputable def pro_unit_left
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((derivedTensor A X).obj (𝟙_ _)).obj K ≅ K := λ_ K

private theorem compared_invertible_of_etale_origin
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (h : Etale.DerivedCategory.isInvertible P.Coefficient X
      (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f)) :
    comparedInvertibilityClause P X (comparedDualizing P f) := by
  let := P.finiteComparedInvertibleExponent (X ↘ Spec (.of P.field.k))
  let := P.finiteComparedInvertibleExponent aY
  let W := Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f
  let N := ((Etale.derivedHom (ModuleCat.{u + 1} P.Coefficient) X).obj
    (Opposite.op W)).obj (𝟙_ _)
  let V := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  have hU := DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
    (Etale.constructibleFiniteTor_tensorUnit P.Coefficient Y)
  have hP := constructibleFiniteTor_rightDerivedUpperShriek P.Coefficient aY f hU
  have hC := (DerivedCategory.constructibleFiniteTor _ X).prop_of_iso
    (rightDerivedUpperShriekComparisonIso P.Coefficient f (𝟙_ _)
      (Etale.constructibleFiniteTor_tensorUnit P.Coefficient Y).1.1.1) hP
  have hW := comparison_reflects_ctf P.Coefficient X W hC
  have hN := finite_hom_ctf P X W (𝟙_ _) hW
    (Etale.constructibleFiniteTor_tensorUnit P.Coefficient X)
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := inverse_hom (ModuleCat.{u + 1} P.Coefficient) X W h
  let η := DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso P.Coefficient X
  refine ⟨V.obj N, DerivedCategory.constructibleFiniteTor_mapDerivedCategory
    P.Coefficient hN, ⟨?_⟩, ⟨?_⟩⟩
  · exact ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso _ W).app N).symm ≪≫
      V.mapIso e₁ ≪≫ η
  · exact ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso _ N).app W).symm ≪≫
      V.mapIso e₂ ≪≫ η

/-- Source-etale locality of cohomological smoothness in the finite purity setting.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality, first assertion
(blueprint: lem-pur-co-smooth-etale-locality).

Proof: use the existing ordinary-etale canonical-map locality theorems, then
transport each clause through the exact comparison functor. Comparison reflects
isomorphisms by exactness and faithfulness on sheaves; its full faithfulness into
bounded-below targets lifts the two inverse isomorphisms at the coefficient unit.
The invertibility and tensor clauses therefore descend by the ordinary-etale
composition results. Construct the inverse globally as RHom(omega_f, unit);
exceptional preservation and the finite-Tor internal-Hom theorem put it in Dctf.
The closed monoidal evaluation identifies it with a tensor inverse, and tensor
comparison transports both inverse isomorphisms to the pro-etale category.

For the third clause, pull the source cover back along each allowed square.
Apply the assumed base-change clause to the pasted square. The composition
criterion for the actual exceptional base-change maps and etale base change
show that the base-change map for f becomes invertible after the exceptional
pullback of the cover. Surjective etale conservativity descends this isomorphism.
All auxiliary schemes remain finite type over the field, without requiring
absolute separatedness after base change. No object is descended or chosen from
a mere existence assertion.
-/
theorem isCohomologicallySmooth_of_surjective_etale
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [U.IsSeparated] [X.IsSeparated]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))] [Etale e]
    [QuasiCompact e] [Surjective e]
    (h : IsCohomologicallySmoothCompared P (e ≫ f)) : IsCohomologicallySmoothCompared P f := by
  let := (P.comparedCompactification e (X ↘ Spec (.of P.field.k))).hasCompactification
  let := (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  let := (P.comparedCompactification (e ≫ f)
    (Y ↘ Spec (.of P.field.k))).hasCompactification
  let := P.finiteComparedInvertibleExponent (U ↘ Spec (.of P.field.k))
  obtain ⟨hω, hθ, hβ⟩ := h
  have he := Etale.isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension
    P.Coefficient (d := 0) e
  have heω := Etale.isInvertible_dualizingComplex P.Coefficient (d := 0) e
  refine ⟨?_, ?_, ?_⟩
  · exact compared_invertible_of_etale_origin P (Y ↘ Spec (.of P.field.k)) f
      (Etale.isInvertible_dualizingComplex_of_comp e f he heω
        (comparison_invertible P U _ hω))
  · intro K hK
    have hc := comparison_reflects_iso P.Coefficient U _ (hθ K hK)
    have := Etale.isIso_dualizingComplexTensorMap_of_comp e f he heω K hc
    exact Functor.map_isIso _ _
  · intro X' Y' _ _ _ _ _ _ g' f' g _ _ _ sq
    let := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
    let : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq
      inferInstance
    have squ : IsPullback (CategoryTheory.Limits.pullback.fst e g')
        (CategoryTheory.Limits.pullback.snd e g') e g' := .of_hasPullback e g'
    have sqh := squ.paste_vert sq
    let U' := CategoryTheory.Limits.pullback e g'
    let e' : U' ⟶ X' := CategoryTheory.Limits.pullback.snd e g'
    let : U'.Over (Spec (.of P.field.k)) := ⟨e' ≫ (X' ↘ Spec (.of P.field.k))⟩
    let : e'.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
    let : (CategoryTheory.Limits.pullback.fst e g').IsOver
        (Spec (.of P.field.k)) := ⟨by
      change _ = e' ≫ (X' ↘ Spec (.of P.field.k))
      rw [← CategoryTheory.comp_over e, ← Category.assoc, squ.w, Category.assoc,
        CategoryTheory.comp_over g']⟩
    let : LocallyOfFiniteType (U' ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (LocallyOfFiniteType (e' ≫ (X' ↘ Spec (.of P.field.k))))
    let : QuasiCompact (U' ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (QuasiCompact (e' ≫ (X' ↘ Spec (.of P.field.k))))
    let : HasCompactification (e' ≫ f') := .of_isPullback sqh
    let : HasInvertibleExponent P.Coefficient U' := .of_hom
      (CategoryTheory.Limits.pullback.fst e g')
    have hh := comparison_reflects_iso P.Coefficient U' _
      (hβ U' Y' (CategoryTheory.Limits.pullback.fst e g') (e' ≫ f') g sqh)
    have := Etale.etaleBaseChange P.Coefficient e squ
    have hhh := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sqh).1 hh
    have hmap := (Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff
      squ sq sqh rfl rfl (𝟙_ _) inferInstance).1 hhh
    have hb := Etale.isIso_of_isIso_rightDerivedUpperShriek_map e'
      (Etale.isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension
        P.Coefficient (d := 0) e')
      (Etale.isInvertible_dualizingComplex P.Coefficient (d := 0) e') _ hmap
    have := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2 hb
    exact Functor.map_isIso _ _

/-- Every etale map in the finite purity setting is cohomologically smooth and has
untwisted relative dualizing object.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality, final assertion
(blueprint: lem-pur-co-smooth-etale-locality).

Proof: the normalized compactification etale adjunction identifies the existing
exceptional inverse image with ordinary pullback by right-adjoint uniqueness.
At the unit, compose with the pullback unit isomorphism and transport through
comparison. The coefficient unit is in Dctf and is its own tensor inverse.
The dimension-zero tensor theorem gives the specified tensor isomorphisms.
Canonical etale normalization and its unit base-change identity give the
exceptional base-change isomorphisms; comparison gives the required maps.
-/
theorem isCohomologicallySmooth_etale_and_dualizing
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))] [Etale e]
    [IsSeparated e] [QuasiCompact e] :
    IsCohomologicallySmoothCompared P e ∧
      Nonempty (@comparedDualizing P U X e
        (P.comparedCompactification e (X ↘ Spec (.of P.field.k))).hasCompactification ≅
        𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} P.Coefficient)))) := by
  let := (P.comparedCompactification e (X ↘ Spec (.of P.field.k))).hasCompactification
  let := P.finiteComparedInvertibleExponent (U ↘ Spec (.of P.field.k))
  let := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  let V := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
  let c := HasCompactification.compactification e
  have : IsIso (Etale.compactificationEtaleComparison P.Coefficient e c) :=
    Etale.isIso_compactificationEtaleComparison P.Coefficient e c
  let w := ((Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} P.Coefficient) e).rightAdjointUniq
      (Etale.compactificationEtaleAdjunction P.Coefficient e c)).app (𝟙_ _) ≪≫
        Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) e
  let η := DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso P.Coefficient U
  let ω : comparedDualizing P e ≅ 𝟙_ _ := V.mapIso w ≪≫ η
  have hunit : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
      U (𝟙_ _) :=
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) U).prop_of_iso η
      (DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
        (Etale.constructibleFiniteTor_tensorUnit P.Coefficient U))
  refine ⟨⟨?_, ?_, ?_⟩, ⟨ω⟩⟩
  · refine ⟨𝟙_ _, hunit, ⟨?_⟩, ⟨?_⟩⟩
    · exact ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) U).mapIso ω).app _ ≪≫
        pro_unit_left _ U _
    · exact ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) U).obj _).mapIso ω ≪≫
        pro_unit_left _ U _
  · intro K _hK
    have := Etale.isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension
      P.Coefficient (d := 0) e K
    exact Functor.map_isIso V _
  · intro U' X' _ _ _ _ _ _ g' e' g _ _ _ sq
    let := ((HasCompactification.compactification e).ofIsPullback sq).hasCompactification
    let : QuasiCompact e' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq
      inferInstance
    have := Etale.etaleBaseChange P.Coefficient e sq
    have := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
      (inferInstance : IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap
        P.Coefficient sq).app (𝟙_ _)))
    exact Functor.map_isIso _ _

end AlgebraicGeometry.ProEtale
