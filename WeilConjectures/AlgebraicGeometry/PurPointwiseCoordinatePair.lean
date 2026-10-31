/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralRepresentingPairData
import WeilConjectures.AlgebraicGeometry.PurCoordinateIntegralInput
import WeilConjectures.AlgebraicGeometry.PurSuppliedSystemRecognition
import WeilConjectures.AlgebraicGeometry.PurFiniteCoordinateCounit
import WeilConjectures.AlgebraicGeometry.PurSupportPresentationAlpha
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.PbcUniformCompleteTriangulated

/-! # Coordinate representing families

Source: blueprint integral adjunction, coordinate Hom chain and actual counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

section Abstract
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] {N : Type u₂} [Category.{v₂} N]
  {F : C ⥤ N} {T : N ⥤ C}

private def unitHomEquiv (a : F ⊣ T) (K L : C) [IsIso (a.unit.app L)] :
    (F.obj K ⟶ F.obj L) ≃ (K ⟶ L) :=
  (a.homEquiv K (F.obj L)).trans
    (Iso.homCongr (Iso.refl K) (asIso (a.unit.app L)).symm)

private theorem unitHomEquiv_apply (a : F ⊣ T) (K L : C) [IsIso (a.unit.app L)]
    (d : F.obj K ⟶ F.obj L) :
    unitHomEquiv a K L d = a.unit.app K ≫ T.map d ≫ inv (a.unit.app L) := by
  simp only [unitHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Adjunction.homEquiv_unit, Iso.refl_inv, Category.id_comp, asIso_inv, Iso.symm_hom,
    Category.assoc]

private theorem unitHomEquiv_reduction (a : F ⊣ T) (K L : C)
    [IsIso (a.unit.app L)] (b : K ⟶ L) : unitHomEquiv a K L (F.map b) = b := by
  rw [unitHomEquiv_apply]
  have h := a.unit.naturality b
  dsimp only [Functor.id_map, Functor.comp_map] at h
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem unitHomEquiv_map (a : F ⊣ T) (K L : C) [IsIso (a.unit.app L)]
    (d : F.obj K ⟶ F.obj L) : F.map (unitHomEquiv a K L d) = d := by
  apply (unitHomEquiv a K L).injective
  rw [unitHomEquiv_reduction]

private theorem unitHomEquiv_natural (a : F ⊣ T) (K K' L : C)
    [IsIso (a.unit.app L)] (b : K' ⟶ K) (d : F.obj K ⟶ F.obj L) :
    unitHomEquiv a K' L (F.map b ≫ d) = b ≫ unitHomEquiv a K L d := by
  rw [unitHomEquiv_apply, unitHomEquiv_apply, Functor.map_comp]
  have h := a.unit.naturality b
  dsimp only [Functor.id_map, Functor.comp_map] at h
  simp only [← Category.assoc]
  rw [← h]

end Abstract

attribute [local irreducible] Padic coordinates purCoefficientModel
  integralExceptionalCoordinates coefficientSequenceLimit
  PurIntegralSupportComparison.beta supportPresentation

private theorem coordinateUnit_iso (W : Scheme.{u})
    (R : CoefficientDerivedSystemCalculus l E W)
    (L : CondensedERealization.Integral l E W) :
    IsIso ((adjunction l E W R).unit.app L.obj) := by
  have hu := (purNormalizedReconstructionOfScheme l E W R).2
    ((purCoefficientModel l E W).functor.obj L.obj)
    ((purCoefficientModel_predicates l E W L.obj).1.mp L.property.1)
  dsimp only [adjunction]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  infer_instance

set_option maxHeartbeats 1600000 in
-- The coordinate Hom assembly needs a larger budget for its categorical rewrites.
/-- A single supplied system represents compact support in quotient coordinates.
Source: current blueprint sk-prop-sp-integral-adjunction, Hom display and final
unit/counit paragraph (blueprint: lem-pur-pointwise-coordinate-pair).

Proof plan: first apply the coordinate-integral-input and supplied-system-recognition
lemmas. Transfer the lower bound through the supplied comparison, then use intrinsic
completeness and normalized reconstruction to invert the coordinate unit. Transfer
the compact-support model's preservation property through the support presentation
and obtain invertibility of the comparison alpha. Compose the full-subcategory Hom
identification, inverse reduction adjunction Hom equivalence, supplied theta, Brown
Hom map, alpha transport, and inverse reduction on Hom into L. Prove the transpose
formula by unit naturality, input naturality by counit naturality, and additivity and
scalar compatibility using the additive reduction functors and support linearity.
Finally apply finite-coordinate-counit and compact-evaluation naturality to obtain
the reduction and finite trace formulas. The resulting Pair is the required
pointwise object; Family naturality is handled by the parent theorem.
This intermediate is strictly simpler than the parent because it fixes one L and A
and has no input-variable naturality or common-degree square.
-/
theorem pointwiseCoordinatePair
    (p : ℕ) [Fact p.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))]
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite))
    (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L) :
    Nonempty (Pair l E (R X) (R Y) S G H D L A hD) := by
  classical
  let := D.finite
  obtain ⟨hC, hn, hc⟩ := coordinateIntegralInput l E p _hpl k Y (R Y) S.PY D.siteY L
  obtain ⟨theta, ⟨htheta, hnorm⟩, _⟩ := suppliedSystemRecognition l E S G H D
    (R X) (R Y) L A
  have hb : ∃ a : ℤ, ∀ n : ℕ, (exceptionalLevel l E (R Y) S G H D L n).IsGE a := by
    obtain ⟨a, b, hab⟩ := A.bounds
    refine ⟨a, fun n ↦ ?_⟩
    have := (hab n).1
    exact DerivedCategory.TStructure.t.isGE_of_iso (A.phi n) a
  have := coordinateUnit_iso l E Y (R Y) L
  have : Fact (ringChar k).Prime := ⟨by simpa only [ringChar.eq k p] using
    (Fact.out : p.Prime)⟩
  have : Fact (ringChar k ≠ l) := ⟨by simpa only [ringChar.eq k p] using _hpl⟩
  let BY : CondensedERealization.Base k := ⟨Y⟩
  have := CompactSupportCondensedRealization.base_noetherian k BY
  have := (pbcIntegralUniformComplete_isTriangulated l E Y
    (CompactSupportCondensedRealization.base_dimension k BY)
    (CompactSupportCondensedRealization.base_primeUnit l k BY)).1
  have hsupport (K : CondensedERealization.Integral l E X) :
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        ((support l E (R X) S G H D).obj K.obj) :=
    ObjectProperty.prop_of_iso (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E))
      ((supportPresentation l E (R X) S G H D (beta l E S G H D)).app K.obj).symm
      (M.preserves K.obj K.property)
  have halpha (K : CondensedERealization.Integral l E X) :
      IsIso (alpha l E (R X) (R Y) S G H D K.obj) := by
    have hε : IsIso ((R Y).adjunction.counit.app
        ((CompactSupportCondensedRealization.reconstructedSystem l E c R M).obj K)) :=
      ((purNormalizedReconstructionOfScheme l E Y (R Y)).1 _ (M.normalized K)).2
    have hpub : IsIso ((CompactSupportCondensedRealization.alpha l E c R M).app K) := by
      dsimp only [CompactSupportCondensedRealization.alpha, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance
    have hp := supportPresentation_alpha l E S G H D R M K
    have hcomp : IsIso (alpha l E (R X) (R Y) S G H D K.obj ≫
        (beta l E S G H D).hom.app
          ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj))) := by
      rw [← hp]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((beta l E S G H D).hom.app
        ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)))
  obtain ⟨hbound, hfinite⟩ := finiteCoordinateCounit l E S G H D hD
    ((reduction l E Y (R Y)).obj L.obj) hC hn hc hb
  have := halpha
  let e (K : CondensedERealization.Integral l E X) :
      (K ⟶ A.object) ≃ ((support l E (R X) S G H D).obj K.obj ⟶ L.obj) :=
    (show (K ⟶ A.object) ≃ (K.obj ⟶ (totalLimit l E X).obj A.system) from
      { toFun := fun h ↦ h.hom
        invFun := fun h ↦ ObjectProperty.homMk h
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }).trans
      (((adjunction l E X (R X)).homEquiv K.obj A.system).symm.trans
        ((Iso.homCongr (Iso.refl _) theta).trans
          ((D.hom _ hC hn hc hb _
            (coordinateIntegralInput l E p _hpl k X (R X) S.PX D.siteX K).1).trans
            ((Iso.homCongr (asIso (alpha l E (R X) (R Y) S G H D K.obj)).symm
              (Iso.refl _)).trans
              (unitHomEquiv (adjunction l E Y (R Y))
                ((support l E (R X) S G H D).obj K.obj) L.obj)))))
  have heSystem (K : CondensedERealization.Integral l E X) (h : K ⟶ A.object) :
      e K h = unitHomEquiv (adjunction l E Y (R Y))
        ((support l E (R X) S G H D).obj K.obj) L.obj
        (alpha l E (R X) (R Y) S G H D K.obj ≫
          D.compact.functor.map ((reduction l E X (R X)).map h.hom ≫
            (adjunction l E X (R X)).counit.app A.system ≫ theta.hom) ≫
          D.counit _ hC hn hc hb) := by
    dsimp only [e, Equiv.trans_apply, Equiv.coe_fn_mk, Iso.homCongr, Iso.symm,
      Iso.refl, asIso]
    rw [Adjunction.homEquiv_counit]
    dsimp only [Supplied.object, support, Functor.comp_obj]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [brown, Functor.comp_obj]
    rw [hD.hom_formula]
  have he (K : CondensedERealization.Integral l E X) (h : K ⟶ A.object) :
      e K h = transpose l E (R X) (R Y) S G H D L A theta
        (D.counit _ hC hn hc hb) (coordinateUnit_iso l E Y (R Y) L) K h := by
    rw [heSystem, unitHomEquiv_apply]
    rfl
  have henat (K K' : CondensedERealization.Integral l E X) (b : K' ⟶ K)
      (h : K ⟶ A.object) :
      e K' (b ≫ h) = (support l E (R X) S G H D).map b.hom ≫ e K h := by
    rw [heSystem, heSystem]
    have ha := (adjunction l E Y (R Y)).counit.naturality
      (D.compact.functor.map ((reduction l E X (R X)).map b.hom))
    change (reduction l E Y (R Y)).map ((support l E (R X) S G H D).map b.hom) ≫
      alpha l E (R X) (R Y) S G H D K.obj =
      alpha l E (R X) (R Y) S G H D K'.obj ≫
        D.compact.functor.map ((reduction l E X (R X)).map b.hom) at ha
    have ht : alpha l E (R X) (R Y) S G H D K'.obj ≫
        D.compact.functor.map ((reduction l E X (R X)).map (b ≫ h).hom ≫
          (adjunction l E X (R X)).counit.app A.system ≫ theta.hom) ≫
        D.counit _ hC hn hc hb =
      (reduction l E Y (R Y)).map ((support l E (R X) S G H D).map b.hom) ≫
        (alpha l E (R X) (R Y) S G H D K.obj ≫
          D.compact.functor.map ((reduction l E X (R X)).map h.hom ≫
            (adjunction l E X (R X)).counit.app A.system ≫ theta.hom) ≫
          D.counit _ hC hn hc hb) := by
      simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc]
      rw [← Category.assoc (alpha l E (R X) (R Y) S G H D K'.obj), ← ha]
      simp only [Category.assoc]
    rw [ht, unitHomEquiv_natural]
  have := M.additive
  have := M.linear
  have := Functor.additive_of_iso
    (supportPresentation l E (R X) S G H D (beta l E S G H D)).symm
  have := Functor.linear_of_iso (PbcIntegralRing l E)
    (supportPresentation l E (R X) S G H D (beta l E S G H D)).symm
  let hom (K : CondensedERealization.Integral l E X) :
      (K ⟶ A.object) ≃ₗ[PbcIntegralRing l E]
        ((support l E (R X) S G H D).obj K.obj ⟶ L.obj) :=
    { e K with
      map_add' := by
        intro a b
        have hea := henat A.object K a (𝟙 A.object)
        have heb := henat A.object K b (𝟙 A.object)
        have heab := henat A.object K (a + b) (𝟙 A.object)
        simp only [Category.comp_id] at hea heb heab
        change e K (a + b) = e K a + e K b
        rw [hea, heb]
        simpa only [show (a + b).hom = a.hom + b.hom from rfl,
          Functor.map_add, Preadditive.add_comp] using heab
      map_smul' := by
        intro r a
        have hea := henat A.object K a (𝟙 A.object)
        have hera := henat A.object K (r • a) (𝟙 A.object)
        simp only [Category.comp_id] at hea hera
        change e K (r • a) = r • e K a
        rw [hea]
        simpa only [show (r • a).hom = r • a.hom from rfl,
          Functor.map_smul, Linear.smul_comp] using hera }
  have htrace :
      (reduction l E Y (R Y)).map (hom A.object (𝟙 A.object)) =
        alpha l E (R X) (R Y) S G H D A.object.obj ≫
          D.compact.functor.map ((adjunction l E X (R X)).counit.app A.system) ≫
          D.compact.functor.map theta.hom ≫ D.counit _ hC hn hc hb := by
    change (reduction l E Y (R Y)).map (e A.object (𝟙 A.object)) = _
    rw [heSystem]
    dsimp only [Supplied.object, support, Functor.comp_obj]
    rw [unitHomEquiv_map]
    change alpha l E (R X) (R Y) S G H D ((totalLimit l E X).obj A.system) ≫
      D.compact.functor.map ((reduction l E X (R X)).map
        (𝟙 ((totalLimit l E X).obj A.system)) ≫
        (adjunction l E X (R X)).counit.app A.system ≫ theta.hom) ≫
        D.counit _ hC hn hc hb = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp]
    simp only [Category.assoc]
  refine ⟨{
    theta := theta
    theta_evaluation := htheta
    theta_normalization := hnorm
    origin := hC
    normalized := hn
    finiteTor := hc
    lowerBound := hb
    unit_iso := coordinateUnit_iso l E Y (R Y) L
    support_integral := hsupport
    alpha_iso := halpha
    hom := hom
    hom_formula := he
    hom_natural := henat
    trace_reduction := htrace
    finite_etale_bound := hbound
    trace_evaluation := ?_ }⟩
  intro n
  let QY := D.siteY.proEvaluation.evaluation n ⋙ (D.siteY.realization n).derived
  let QX := D.siteX.proEvaluation.evaluation n ⋙ (D.siteX.realization n).derived
  let Fn := FiniteCoefficientAdjoints.lower
    (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) n) c
  have ht : QX.map theta.hom ≫
      (D.siteX.realization n).derived.map
        ((D.evaluation n).hom.app ((reduction l E Y (R Y)).obj L.obj)) =
      (D.siteX.realization n).derived.map (A.phi n).hom := by
    dsimp only [QX, Functor.comp_map]
    rw [htheta n, ← Functor.map_comp]
    dsimp only [levelMap, exceptionalLevel, Functor.comp_obj]
    rw [Category.assoc, Iso.inv_hom_id_app]
    apply congrArg (D.siteX.realization n).derived.map
    exact Category.comp_id (A.phi n).hom
  have ht' : Fn.map (QX.map theta.hom) ≫
      Fn.map ((D.siteX.realization n).derived.map
        ((D.evaluation n).hom.app ((reduction l E Y (R Y)).obj L.obj)) ≫
        (finiteCoordinates l E S G H D hD n).hom.app
          ((D.siteY.proEvaluation.evaluation n).obj ((reduction l E Y (R Y)).obj L.obj))) =
      Fn.map ((D.siteX.realization n).derived.map (A.phi n).hom ≫
        (finiteCoordinates l E S G H D hD n).hom.app
          ((D.siteY.proEvaluation.evaluation n).obj ((reduction l E Y (R Y)).obj L.obj))) := by
    rw [← Fn.map_comp, ← Category.assoc, ht]
  have hnat := (D.compactEvaluation n).hom.naturality theta.hom
  change QY.map (D.compact.functor.map theta.hom) ≫
      (D.compactEvaluation n).hom.app _ =
    (D.compactEvaluation n).hom.app A.system ≫ Fn.map (QX.map theta.hom) at hnat
  have hf := hfinite n
  change QY.map (D.counit _ hC hn hc hb) =
    (D.compactEvaluation n).hom.app _ ≫ Fn.map _ ≫ _ at hf
  change QY.map ((reduction l E Y (R Y)).map (hom A.object (𝟙 A.object))) = _
  rw [htrace]
  dsimp only [QY, QX, Fn, Supplied.object, support, exceptionalLevel, brown,
    Functor.comp_obj, Functor.comp_map] at hf ht' hnat ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [hf]
  rw [← Category.assoc
    ((D.siteY.realization n).derived.map
      ((D.siteY.proEvaluation.evaluation n).map (D.compact.functor.map theta.hom))), hnat]
  simp only [Category.assoc]
  rw [reassoc_of% ht']
  simp only [Functor.map_comp, Category.assoc]

end WeilConjectures.PurIntegralRepresentingPair
