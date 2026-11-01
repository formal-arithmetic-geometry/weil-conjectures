/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteCoefficientSmoothPurity
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.PurityTensorMapNaturality
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Naturality and choice-independence of the smooth purity map

Source: Weil conjectures blueprint, sec-smooth-purity/sk-thm-smooth-purity,
proposition `prop-pur-smooth-purity-naturality-cover`, order 2015
(blueprint: prop-pur-smooth-purity-naturality-cover).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

private theorem tensorShiftGeneric_naturality
    (C : Type uC) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (r : ℤ) {M N : _root_.DerivedCategory C} (a : M ⟶ N)
    (T : _root_.DerivedCategory C) :
    (smoothPurityTensorShiftGeneric C r M T).hom ≫
        ((curriedTensor (_root_.DerivedCategory C)).map a).app T =
      (shiftFunctor _ r).map
          (((curriedTensor (_root_.DerivedCategory C)).map a).app (T⟦-r⟧)) ≫
        (smoothPurityTensorShiftGeneric C r N T).hom := by
  let F := curriedTensor (_root_.DerivedCategory C)
  let := _root_.DerivedCategory.commShiftTensorLeft C M
  let := _root_.DerivedCategory.commShiftTensorLeft C N
  have h := NatTrans.shift_app_comm (F.map a) r (T⟦-r⟧)
  have hi : ((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫
      (F.map a).app ((T⟦-r⟧)⟦r⟧) =
      (shiftFunctor _ r).map ((F.map a).app (T⟦-r⟧)) ≫
        ((F.obj N).commShiftIso r).inv.app (T⟦-r⟧) := by
    rw [← cancel_mono (((F.obj N).commShiftIso r).hom.app (T⟦-r⟧))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  change (((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫
      (F.obj M).map ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)) ≫
        (F.map a).app T =
    (shiftFunctor _ r).map ((F.map a).app (T⟦-r⟧)) ≫
      (((F.obj N).commShiftIso r).inv.app (T⟦-r⟧) ≫
        (F.obj N).map ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T))
  have hn := (F.map a).naturality
    ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)
  calc
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg
      (fun z ↦ ((F.obj M).commShiftIso r).inv.app (T⟦-r⟧) ≫ z) hn
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun z ↦ z ≫ (F.obj N).map
        ((shiftFunctorCompIsoId _ (-r) r (neg_add_cancel r)).hom.app T)) hi
    _ = _ := Category.assoc _ _ _

/-- The specified tensor-shift comparison commutes with maps in its first factor.
Source: the canonical bifunctor shift structure, as used in step 2 of
`prop-pur-smooth-purity-naturality-cover`. -/
private theorem smoothPurityTensorShift_naturality
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (r : ℤ)
    {M N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N)
    (T : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (smoothPurityTensorShift A X r M T).hom ≫
        ((smoothPurityTensor A X).map a).app T =
      (shiftFunctor _ r).map (((smoothPurityTensor A X).map a).app (T⟦-r⟧)) ≫
        (smoothPurityTensorShift A X r N T).hom := by
  have hM := (existsUnique_smoothPurityTensorShift (ModuleCat.{u + 1} A) X r M T).exists
    |>.choose_spec
  have hN := (existsUnique_smoothPurityTensorShift (ModuleCat.{u + 1} A) X r N T).exists
    |>.choose_spec
  have eM := eq_of_heq hM
  have eN := eq_of_heq hN
  unfold smoothPurityTensorShift smoothPurityTensorShiftCoefficients
  rw [eM, eN]
  exact tensorShiftGeneric_naturality _ r a T

private theorem finiteOrigin (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    ∃ J : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)),
      ∃ _e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅
            (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K,
        _root_.DerivedCategory.TStructure.t.plus J ∧
          ProEtale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} P.Coefficient) Y
              ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) := by
  classical
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  have hc := (Scheme.finiteRing_constructibleDerived_origin Y P.Ring).2.2.1 K
  have hOrigin : (ObjectProperty.ι
      (Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison Y P.Ring).essImage K := by
    apply hc.mpr
    refine ⟨hK.1.2, ?_⟩
    obtain ⟨a, ha⟩ := hK.1.1.bddBelow
    obtain ⟨b, hb⟩ := hK.1.1.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge ((min_le_left a b).trans (ha hn))) hi
    · exact (not_lt_of_ge ((hb hn).trans (le_max_right a b))) hi
  obtain ⟨J, ⟨eJ⟩⟩ := hOrigin
  let : (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring).Additive
  let ecomp := (Functor.mapDerivedCategoryCompIso ν
    (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor).app J.obj
  let e : ν.mapDerivedCategory.obj J.obj ≅ E.inverse.obj K :=
    E.functor.preimageIso (ecomp.symm ≪≫ eJ ≪≫ (E.counitIso.app K).symm)
  obtain ⟨c, d, _, hz⟩ := J.property.2
  have hplus : _root_.DerivedCategory.TStructure.t.plus J.obj :=
    ⟨c, (_root_.DerivedCategory.isGE_iff J.obj c).mpr (fun i hi ↦ hz i (.inl hi))⟩
  have hbc : Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} P.Coefficient) Y J.obj := by
    refine ⟨⟨hplus, d, ?_⟩, ?_⟩
    · exact (_root_.DerivedCategory.isLE_iff J.obj d).mpr (fun i hi ↦ hz i (.inr hi))
    · intro i
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (J.property.1 i)
  have hbc' : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} P.Coefficient) Y (E.inverse.obj K) :=
    (ProEtale.DerivedCategory.boundedConstructible_iff _ _ _).mpr ⟨J.obj, hbc, ⟨e⟩⟩
  obtain ⟨a, b, ht⟩ := hK.2
  have ht' : Scheme.HasProEtaleTorAmplitude Y P.Ring
      (E.functor.obj (E.inverse.obj K)) a b := by
    refine ⟨ht.1, ?_⟩
    intro L Q hL f hf hQ M i hi
    obtain ⟨eL⟩ := hL
    exact ht.2 L Q ⟨eL ≪≫ E.counitIso.app K⟩ f hf hQ M i hi
  have ht'' := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    P.Ring Y a b ht.1 (E.inverse.obj K)).mp ht'
  exact ⟨J.obj, e, hplus, hbc', a, b, ht''⟩

/-- Naturality of the canonical smooth purity map in the coefficient object.
Source: the naturality square in the proof of
`prop-pur-smooth-purity-naturality-cover` (blueprint:
`prop-pur-smooth-purity-naturality-cover`).

The proof is the projection-mate square followed by the canonical tensor-shift
comparison; this is strictly the first conjunct of the parent proposition. -/
private theorem smoothPurityMap_naturality_part
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
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
    (K K' : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos Y K)
    (hK' : finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos Y K')
    (u : K ⟶ K') :
    P.smoothPurityMap f d K hK ≫
        (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
            ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map u)) =
      (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((shiftFunctor _ (2 * (d : ℤ))).map
            (((smoothPurityTensor P.Coefficient X).map
              ((P.smoothPurityPullback f).map
                ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map u))).app
              ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))) ≫
        P.smoothPurityMap f d K' hK' := by
  classical
  obtain ⟨J, e, hJ, hctf⟩ := finiteOrigin P Y K hK
  obtain ⟨J', e', hJ', hctf'⟩ := finiteOrigin P Y K' hK'
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
  obtain ⟨a, ha⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
    J J' hJ').2 (e.hom ≫ E.inverse.map u ≫ e'.inv)
  change ν.map a = e.hom ≫ E.inverse.map u ≫ e'.inv at ha
  have ha' : ν.map a ≫ e'.hom = e.hom ≫ E.inverse.map u := by
    rw [ha, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := (P.purityTensorMap_naturality f d _ _ hctf hctf'
    (E.inverse.map u) J J' e e' a ha').1
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  let : HasCompactification f := inferInstance
  let F := smoothPurityTensor P.Coefficient X
  let m := (P.smoothPurityPullback f).map (E.inverse.map u)
  change P.smoothPurityTheta f (E.inverse.obj K) J e ≫
    (P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
      (E.inverse.map u) =
      (F.map m).app (P.diagonalDualizing f) ≫
        P.smoothPurityTheta f (E.inverse.obj K') J' e' at hn
  have hp : P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
        (E.inverse.obj K) J e ≫
        (P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
          (E.inverse.map u) =
      (F.map m).app (P.diagonalTwist X d) ≫
        P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
          (E.inverse.obj K') J' e' := by
    change ((F.obj ((P.smoothPurityPullback f).obj (E.inverse.obj K))).map
      (P.diagonalDualizingObject d f (Y ↘ Spec (.of P.field.k))).inv ≫
      P.smoothPurityTheta f (E.inverse.obj K) J e) ≫ _ = _
    have ho := (F.map m).naturality
      (P.diagonalDualizingObject d f (Y ↘ Spec (.of P.field.k))).inv
    calc
      _ = _ := Category.assoc _ _ _
      _ = _ := congrArg (fun z ↦ (F.obj
        ((P.smoothPurityPullback f).obj (E.inverse.obj K))).map
          (P.diagonalDualizingObject d f (Y ↘ Spec (.of P.field.k))).inv ≫ z) hn
      _ = _ := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun z ↦ z ≫ P.smoothPurityTheta f
        (E.inverse.obj K') J' e') ho
      _ = _ := Category.assoc _ _ _
  let R := (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor
  have ht : P.smoothPurityTensorMap f d K hK ≫
      R.map ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (E.inverse.map u)) =
      R.map ((F.map m).app (P.diagonalTwist X d)) ≫
        P.smoothPurityTensorMap f d K' hK' := by
    unfold smoothPurityTensorMap
    rw [(P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose_spec J e,
      (P.existsUnique_smoothPurityTensorMap f d K' hK').exists.choose_spec J' e',
      ← R.map_comp, ← R.map_comp, hp]
  have hs := smoothPurityTensorShift_naturality P.Coefficient X (2 * (d : ℤ))
    m (P.diagonalTwist X d)
  change (P.smoothPurityReassociation X d
      ((P.smoothPurityPullback f).obj (E.inverse.obj K))).hom ≫
        (F.map m).app (P.diagonalTwist X d) =
    (shiftFunctor _ (2 * (d : ℤ))).map
        ((F.map m).app ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧)) ≫
      (P.smoothPurityReassociation X d
        ((P.smoothPurityPullback f).obj (E.inverse.obj K'))).hom at hs
  unfold smoothPurityMap
  rw [Category.assoc, ht, ← Category.assoc, ← R.map_comp]
  exact (congrArg (fun z ↦ R.map z ≫ P.smoothPurityTensorMap f d K' hK') hs).trans
    (by rw [R.map_comp, Category.assoc])

/-- The canonical smooth purity map is natural in the coefficient object, and its
presentation-level formula is independent of all choices of an etale presentation.
Source: Weil conjectures blueprint, sec-smooth-purity/sk-thm-smooth-purity,
proposition `prop-pur-smooth-purity-naturality-cover`, order 2015
(blueprint: prop-pur-smooth-purity-naturality-cover).

Proof (the node's six steps; composition below is right to left, as in the node).
1. Write `M_K = Lf^*K`, `T = Λ_X(d)[2d]`, `ω = Rf^!Λ_Y`, and `γ_K = θ_K (1 ⊗ Π_f⁻¹) τ_K`
   (def-pur-smooth-purity-map). The adjoint of `θ_K` under `Rf_! ⊣ Rf^!` is `a_K`: tensor
   symmetry, the inverse projection map `PF⁻¹`, the fixed counit `ε_{f,Λ_Y} ⊗ 1_K` and the
   unitor (def-pur-co-smoothness). For `u : K ⟶ K'` and `m = Lf^*u`, naturality of the
   projection isomorphism (fix-prop-projection-formula), symmetry and unitors gives
   `u a_K = a_{K'} Rf_!(m ⊗ 1_ω)`. Transposing through the natural Hom bijection
   (thm-sf-ambient-adjoint-class) gives `Rf^!u θ_K = θ_{K'} (m ⊗ 1_ω)`; the tensor formula
   (thm-pur-cohomological-smoothness) applies on this smooth finite-coefficient domain.
2. With `L = Λ_X(d)`, `τ_K` is the shift identification `(M_K ⊗ L)[2d] ≅ M_K ⊗ L[2d]`. On a
   K-flat model the total differentials `d_P ⊗ 1 + (-1)^p 1 ⊗ d_L` agree since `L` sits in
   degree zero and `2d` is even, and the identity commutes with maps in the first factor, so
   `τ_{K'} (m ⊗ 1_L)[2d] = (m ⊗ 1_T) τ_K`. By the bifunctor law
   (lem-weil-derived-tensor-functorial), `(m ⊗ 1_ω)(1 ⊗ Π_f⁻¹) = (1 ⊗ Π_f⁻¹)(m ⊗ 1_T)`.
3. Pasting: `Rf^!u γ_K = θ_{K'} (m ⊗ 1_ω)(1 ⊗ Π_f⁻¹) τ_K = θ_{K'} (1 ⊗ Π_f⁻¹)(m ⊗ 1_T) τ_K
   = γ_{K'} (m ⊗ 1_L)[2d]`, the first conjunct (in Lean's left-to-right order).
4. `Π_f` is the specified diagonal orientation (thm-pur-diagonal-dualizing-object); the DNC
   comparison normalized on standard pairs is unique (thm-pur-dnc-invariance; `X` is
   Noetherian by lem-weil-pbc-finite-type-over-noetherian and `ℓ ≠ char k`), and the
   vector-bundle integration is unique (thm-amb-vector-bundle-purity). So coordinate, cover
   or frame choices do not change `Π_f`; no arbitrary isomorphism `ω ≅ T` is selected.
5. Changing a K-flat model of `M_K` is absorbed by the canonical resolution comparison with
   its identity and cocycle laws (lem-weil-derived-tensor-resolution-independent); tensoring
   `Π_f⁻¹` and the shift identification commute with these comparisons.
6. The adjoint `a_K` determines `θ_K` by injectivity of the Hom bijection; changing the
   compactification or etale-origin witness identifies the Hom bijections canonically
   (thm-sf-ambient-adjoint-class), compatibly with the projection formula. Hence, for any two
   etale representatives `K₀`, `K₀'` with comparison isomorphisms `e`, `e'`, the two
   presentation composites `(1 ⊗ Π_f⁻¹) ≫ θ` agree, which is the second conjunct.
-/
theorem smoothPurityMap_naturality_choice_independence
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
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
    (K K' : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos Y K)
    (hK' : finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos Y K')
    (u : K ⟶ K') :
    P.smoothPurityMap f d K hK ≫
        (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
            ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map u)) =
      (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((shiftFunctor _ (2 * (d : ℤ))).map
            (((smoothPurityTensor P.Coefficient X).map
              ((P.smoothPurityPullback f).map
                ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map u))).app
              ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))) ≫
        P.smoothPurityMap f d K' hK' ∧
    ∀ (K₀ K₀' : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (e : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅
          (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
      (e' : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀' ≅
          (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K),
      P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) K₀ e =
        P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) K₀' e' := by
  constructor
  · exact smoothPurityMap_naturality_part P f d K K' hK hK' u
  · intro K₀ K₀' e e'
    have h₁ := (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose_spec K₀ e
    have h₂ := (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose_spec K₀' e'
    exact h₁.symm.trans h₂

end WeilConjectures.PurityFiniteSetting
