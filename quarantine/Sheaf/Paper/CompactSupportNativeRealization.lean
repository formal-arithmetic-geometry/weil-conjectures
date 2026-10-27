/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.CompactSupportScalarLimitFoundations
import all Sheaf.Paper.CompactSupportFiniteAction
import all Sheaf.Paper.CoefficientSequenceRoosModel
import all Sheaf.Paper.CompactSupportReductionTower
import Sheaf.Paper.CompactSupportInputTowerCompatibility
import Sheaf.Paper.CompactSupportCoefficientTransition

/-! # Normalized realization of a specified native support tower

Source: Stacks Tags 0940 and 0941; the native realization construction in
compactSupport_normalized_realization, applied to the supplied reduction calculus.
(blueprint: lem-pur-compact-support-native-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard constantSheaf Padic.coefficientExtensionIdeal
  coefficientSequenceEvaluation coefficientSequenceTransition
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence Functor.objPreimage Functor.objObjPreimageIso

/-- The normalized realization can use any specified reduction calculus. Its underlying
completed tower is exactly the native tower, including every positive exponent.
Source: Stacks Tags 0940, 0941; compactSupport_normalized_realization, native construction.
(blueprint: lem-pur-compact-support-native-realization).
Proof: evaluate the native proper/open coefficient system. The native transition formula
and the supplied reduction calculus identify its quotient transitions with the normalized
compact-support transitions. Their finite-action normalization gives a normalized DVR
tower with this exact underlying tower. Choose a complex representing the native system;
its exact finite evaluations give the finite complexes, chain maps, and their comparison
isomorphisms. Exact scalar restriction gives the strict completed tower. Localization
factorization proves the chain transition equation; the ordinary restriction composition
identity proves the completed transition equation degree by degree. -/
theorem compactSupport_native_realization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) (hK : sfIntegralConstructible l E X K) :
    ∃ R : CoefCompactSupportRealization l E D hl c K,
      CoefCompactSupportRealizationSpec l E D hl c K R ∧
      R.normalized.tower = (PurStrictScalar.scalarSupportCompletedTower l E c S).obj K := by
  classical
  have hlk : IsUnit (l : D.k) := PurCompactSupport.coefficientPrimeUnit l D hl
  let _hK := hK
  let N : coefficientSequenceDerived.{u, u} l E Y :=
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K)
  let e (n : ℕ) : (coefficientSequenceDerivedEvaluation l E Y n).obj N ≅
      coefCompactSupportLevel l E c K n :=
    (compactSupportSystemEvaluation l E c n).app (S.reduction.obj K) ≪≫
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        ((S.reductionEvaluation n).app K)
  have he {m n : ℕ} (h : n ≤ m) :
      (coefficientSequenceDerivedTransition l E Y h).app N ≫
        (normalizedDVRRes l E Y h).map (e n).hom =
      (e m).hom ≫ coefCompactSupportNormalizedTau l E c K h := by
    have hg := compactSupportNativeSystemTransition l E c h (S.reduction.obj K)
    have hd := compactSupportReductionTransition l E X S.toCoefficientDerivedSystemReduction h K
    have H := compactSupportFiniteSquare
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)))
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
      (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E X m n h))
      (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n h))
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom
      _ _ _ _ _ _ _ hg hd
    have H' : (compactSupportCoefficientTransition l E Y h).app N ≫
        (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n h)).map
          (e n).hom = (e m).hom ≫ coefCompactSupportTau l E c K h := by
      simpa only [N, coefCompactSupportTau, coefficientFiniteDerivedExtension, e,
        Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
        Category.assoc] using H
    apply (cancel_mono ((coefCompactSupportRestrictionIso l E Y h).hom.app
      (coefCompactSupportLevel l E c K n))).mp
    rw [Category.assoc, (coefCompactSupportRestrictionIso l E Y h).hom.naturality]
    rw [← Category.assoc]
    have hτ := NatTrans.congr_app (derivedTransition_direct l E Y h) N
    change (coefficientSequenceDerivedTransition l E Y h).app N ≫
      (coefCompactSupportRestrictionIso l E Y h).hom.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N) = _ at hτ
    rw [hτ]
    simp only [coefCompactSupportNormalizedTau, Category.assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact H'
  let T : NormalizedDVRTower l E Y D hl := {
    M := fun n ↦ (coefficientSequenceDerivedEvaluation l E Y n).obj N
    tau := fun h ↦ (coefficientSequenceDerivedTransition l E Y h).app N
    tau_refl := derivedTransition_id l E Y N
    tau_comp := fun h₁ h₂ ↦ derivedTransition_comp l E Y N h₁ h₂
    tower := (coefficientSequenceDerivedRestriction l E Y).obj N
    evaluationIso := fun n ↦ (coefficientRestrictedEvaluationIso l E Y n).app N
    tower_tau := fun h ↦ derivedRestrictedTransition l E Y D hl N h
    normalization := compactSupportSystem_normalized l c D.k hlk E ⟨K, _hK⟩ S }
  obtain ⟨P, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q N
  let C (n : ℕ) :=
    ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P
  let j (n : ℕ) : DerivedCategory.Q.obj (C n) ≅ coefCompactSupportLevel l E c K n :=
    ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.app P).symm ≪≫
      (coefficientSequenceDerivedEvaluation l E Y n).mapIso i ≪≫ e n
  let t {m n : ℕ} (h : n ≤ m) : C m ⟶
      ((normalizedDVRModuleRes l E Y h).mapHomologicalComplex (.up ℤ)).obj (C n) :=
    (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E Y h) (.up ℤ)).app P
  let U := coefficientSequenceRestriction l E Y
  let Q := (U.mapHomologicalComplex (.up ℤ)).obj P
  let q : DerivedCategory.Q.obj Q ≅ T.tower :=
    (U.mapDerivedCategoryFactors.app P).symm ≪≫
      (coefficientSequenceDerivedRestriction l E Y).mapIso i
  let v (n : ℕ) :
      (((evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E Y D hl)).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((completedIntegralRestrictScalars l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj
        (C n) :=
    (NatIso.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)) (.up ℤ)).app P
  let R : CoefCompactSupportRealization l E D hl c K := {
    normalized := T
    levels := e
    complexes := C
    identifications := j
    chainMaps := fun h ↦ t h
    strict := Q
    strictIso := q
    strictEvaluations := v }
  refine ⟨R, ⟨he, ?_, ?_⟩, rfl⟩
  · intro m n h
    have hf := CategoryTheory.derivedTransition_fac
      (coefficientSequenceEvaluation l E Y m) (coefficientSequenceEvaluation l E Y n)
      (normalizedDVRModuleRes l E Y h) (coefficientSequenceTransition l E Y h) P
    rw [← derivedTransition_eq] at hf
    have hf' : DerivedCategory.Q.map (t h) ≫
        (normalizedDVRModuleRes l E Y h).mapDerivedCategoryFactors.inv.app (C n) ≫
        (normalizedDVRRes l E Y h).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.inv.app P) =
      (coefficientSequenceEvaluation l E Y m).mapDerivedCategoryFactors.inv.app P ≫
        (coefficientSequenceDerivedTransition l E Y h).app (DerivedCategory.Q.obj P) := by
      apply (cancel_epi
        ((coefficientSequenceEvaluation l E Y m).mapDerivedCategoryFactors.hom.app P)).mp
      dsimp only [t]
      rw [← reassoc_of% hf]
      simp only [C, Iso.hom_inv_id_app_assoc]
      change (coefficientSequenceDerivedTransition l E Y h).app (DerivedCategory.Q.obj P) ≫
        (normalizedDVRRes l E Y h).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app P) ≫
        (normalizedDVRRes l E Y h).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.inv.app P) = _
      rw [← Functor.map_comp, Iso.hom_inv_id_app]
      erw [(normalizedDVRRes l E Y h).map_id, Category.comp_id]
    change DerivedCategory.Q.map (t h) ≫
      (normalizedDVRModuleRes l E Y h).mapDerivedCategoryFactors.inv.app (C n) ≫
      (normalizedDVRRes l E Y h).map (j n).hom =
        (j m).hom ≫ coefCompactSupportNormalizedTau l E c K h
    dsimp only [j, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hf']
    have hn := (coefficientSequenceDerivedTransition l E Y h).naturality i.hom
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn, he]
    rfl
  · intro m n h
    change (NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E Y D hl)).map (homOfLE h).op)
      (.up ℤ)).app Q ≫ (v n).hom = (v m).hom ≫
        ((completedIntegralRestrictScalars l E Y D hl m).mapHomologicalComplex (.up ℤ)).map
          (t h) ≫ (Functor.mapHomologicalComplexCompIso
            (coefCompactSupportCompletedModuleComp l E Y D hl h) (.up ℤ)).hom.app (C n)
    have hc : coefCompactSupportCompletedModuleComp l E Y D hl h =
        completedCompO l E Y D hl h := by
      unfold coefCompactSupportCompletedModuleComp completedCompO restrictCompIso
      rfl
    rw [hc]
    apply HomologicalComplex.hom_ext
    intro k
    simp only [Q, U, v, C, t, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, NatIso.mapHomologicalComplex,
      Iso.app_hom, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f]
    exact restrictedTransition l E Y D hl (P.X k) h


end WeilConjectures
