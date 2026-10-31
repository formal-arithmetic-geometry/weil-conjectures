/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.Logic.Function.Basic
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Equivalence
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemsExistence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOperationsExistence
import WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictSystemGeometricRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenWordEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteWordIdentification
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityFiniteLevelProjectionTransport

/-! Finite-level comparison and conservativity for compact-support projection.

Source: paragraph (3) of
`sk-prop-sp-integral-adjunction-direct-image.proof.md`.
(blueprint: lem-sp-tower-compact-support-projection-formula)

The proof evaluates the two transposes at each finite coefficient quotient,
uses the bounded constructible finite-Tor projection theorem and the open
unit/counit triangles, then applies joint conservativity of the tower
calculus. The final mate is the recorded `projection` arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek
open SheafOfModules

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Complete the existing coefficient calculus without changing its systems field. -/
private theorem calculus_extension (b : Base l E) (T : Scheme.{u}) :
    ∃ s : WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T) (tau l E T), s.systems = b.calculus T := by
  classical
  let A := b.calculus T
  let O := (WeilConjectures.SemilinearSections.semilinearOperationsData
    (ProEt.topology T) (SpTowerShriek.B l E T) (tau l E T) A).some
  refine ⟨{
    systems := A
    homTransition := ?_
    tensorNormalization := b.tensorNormalization T
    geometric := ?_
    coefficientExtension := O.coefficientExtension
    localization := O.localization }, rfl⟩
  · apply WeilConjectures.SemilinearSections.homReductionFormula
    intro m n h M N
    exact (WeilConjectures.SemilinearSections.tensor_reduction_formula
      (ProEt.topology T) (SpTowerShriek.B l E T) (tau l E T) A M N h).symm
  · intro C' cat small J' uInv uPush adjSet hlim
    obtain ⟨G, hG⟩ := O.geometric J' uInv uPush adjSet
    exact ⟨G,
      WeilConjectures.SemilinearSections.push_transition_of_pull
        (ProEt.topology T) (SpTowerShriek.B l E T) (tau l E T) A
        J' uInv uPush adjSet G hG,
      hG, WeilConjectures.SemilinearSections.projection_evaluation
        (ProEt.topology T) (SpTowerShriek.B l E T) (tau l E T) A
        J' uInv uPush adjSet G⟩

/-- The three-index laws depend on the normalized calculus, not its existence choice. -/
private theorem strict_system_comparisons (b : Base l E) (o : Operations l E b) :
    StrictSystemComparisons l E b o := by
  refine ⟨calculus_extension l E b, ?_, ?_, ?_⟩
  · intro T K L m n h
    exact WeilConjectures.SemilinearSections.tensor_reduction_formula
      (ProEt.topology T) (SpTowerShriek.B l E T) (tau l E T) (b.calculus T) K L h
  · intro T r m n h k K L
    exact WeilConjectures.SemilinearSections.scalarTensor_composition
      (ProEt.topology T) (SpTowerShriek.B l E T) (tau l E T) (b.calculus T) h k K L
  · intro X Y f r m n h k Q
    let G := (o.geometry f).generic
    exact SpTowerShriek.mate_pasting_with_comparisons
      (G.derivedLevelAdjunction r) (G.derivedLevelAdjunction m)
      (G.derivedLevelAdjunction n)
      (TwoSquare.mk _ _ _ _ (G.coefficientPullback k).hom)
      (TwoSquare.mk _ _ _ _ (G.coefficientPullback h).hom)
      (TwoSquare.mk _ _ _ _ (G.coefficientPullback (h.trans k)).hom)
      ((b.calculus Y).scalarComposition h k).hom
      (G.target.scalarComposition h k).hom
      (G.coefficientPullback_composition
        (ProEt.topology Y) (SpTowerShriek.B l E Y) (tau l E Y) (b.calculus Y)
        (ProEt.topology X)
        (proEtaleSheafInverseImage f (Type (u + 1)))
        (proEtaleSheafDirectImage f (Type (u + 1)))
        (proEtaleSheafAdjunction f (Type (u + 1))) h k) Q

private theorem evaluation_sections (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq (((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.obj U)
      (((spCoefficientEvaluation l E T D.equivalence n).obj M).val.obj U) := by
  dsimp [SpTowerShriek.ev, WeilConjectures.SemilinearSections.evaluation,
    SheafOfModules.pushforward,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, SheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalars, PresheafOfModules.restrictScalarsObj,
    spCoefficientEvaluation, systemEvaluation]
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app, eqToHom_refl]
  exact (b.sections T M n U).trans (D.sections M n U).symm

private theorem hom_function_heq {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {g : M' ⟶ N'} (hfg : HEq f g) :
    HEq (fun x ↦ f x) (fun x ↦ g x) := by
  cases hM
  cases hN
  cases hfg
  rfl

set_option maxHeartbeats 2000000 in
-- Comparing the two concrete ring-presheaf presentations requires unfolding their objects.
private theorem evaluation_restrictions (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V) :
    HEq (fun x ↦
      ((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.map f x)
      (fun x ↦ ((spCoefficientEvaluation l E T D.equivalence n).obj M).val.map f x) := by
  change HEq
    (fun x ↦ ((b.realization T).functor.obj M).val.map
      (Prod.mkHom (𝟙 n) f.unop).op x)
    (fun x ↦ ((D.equivalence.functor.obj M).level n).val.map f x)
  have hB := b.restrictions T M (Prod.mkHom (𝟙 n) f.unop).op
  have hD := D.restrictions M n f
  refine hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (D.sections M n U).symm)) ?_
    (hB.trans hD.symm)
  have hmap :
      ((WeilConjectures.SemilinearSections.ring
        (WeilConjectures.coefficientSequenceTopology (ProEt.topology T))
        (WeilConjectures.SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj.map
            (Prod.mkHom (𝟙 n) f.unop).op).hom =
      ((spCoefficientRing l E T n).obj.map f).hom := by
    change ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((((WeilConjectures.SemilinearSections.rings (ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T)).map (𝟙 (op n))).hom.app U) ≫
          (SpTowerShriek.B l E T n).obj.map f)).hom =
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((SpTowerShriek.B l E T n).obj.map f)).hom
    erw [CategoryTheory.Functor.map_id]
    simp
  rw [hmap]
  exact congrArg (ModuleCat.restrictScalars
    (((spCoefficientRing l E T n).obj).map f).hom).obj
    (eq_of_heq ((b.sections T M n V).trans (D.sections M n V).symm))

set_option maxHeartbeats 2000000 in
-- Evaluation changes scalar actions but leaves these underlying section functions intact.
private theorem evaluation_maps (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    {M N : spCoefficientTowers l E T} (f : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦
      ((SpTowerShriek.ev l E T n).map ((b.realization T).functor.map f)).val.app U x)
      (fun x ↦ ((spCoefficientEvaluation l E T D.equivalence n).map f).val.app U x) := by
  change HEq
    (fun x ↦ ((b.realization T).functor.map f).val.app (op (n, U.unop)) x)
    (fun x ↦ ((D.equivalence.functor.map f).app n).val.app U x)
  exact hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (D.sections M n U).symm))
    (eq_of_heq ((b.sections T N n U).trans (D.sections N n U).symm))
    ((b.morphisms T f (op (n, U.unop))).trans (D.morphisms f n U).symm)

private theorem transport_restriction {A B : Type*} [Ring A] [Ring B]
    (q : A →+* B) {M M' : ModuleCat A} {N N' : ModuleCat B}
    (hM : M = M') (hN : N = N')
    (f : M ⟶ (ModuleCat.restrictScalars q).obj N)
    (g : M' ⟶ (ModuleCat.restrictScalars q).obj N')
    (hfg : HEq (fun x ↦ f x) (fun x ↦ g x)) :
    f ≫ (ModuleCat.restrictScalars q).map (eqToHom hN) = eqToHom hM ≫ g := by
  cases hM
  cases hN
  ext x
  exact congrFun (eq_of_heq hfg) x

private theorem transport_morphism {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') (hfg : HEq (fun x ↦ f x) (fun x ↦ g x)) :
    f ≫ eqToHom hN = eqToHom hM ≫ g := by
  cases hM
  cases hN
  ext x
  exact congrFun (eq_of_heq hfg) x

private def evaluation_object (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) :
    (SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M) ≅
      (spCoefficientEvaluation l E T D.equivalence n).obj M where
  hom := ⟨{
    app := fun U ↦ eqToHom (eq_of_heq (evaluation_sections l E b T D M n U))
    naturality := fun {U V} f ↦ transport_restriction _
      (eq_of_heq (evaluation_sections l E b T D M n U))
      (eq_of_heq (evaluation_sections l E b T D M n V)) _ _
      (evaluation_restrictions l E b T D M n f) }⟩
  inv := ⟨{
    app := fun U ↦ eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm
    naturality := fun {U V} f ↦ transport_restriction _
      (eq_of_heq (evaluation_sections l E b T D M n U)).symm
      (eq_of_heq (evaluation_sections l E b T D M n V)).symm _ _
      (evaluation_restrictions l E b T D M n f).symm }⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]

private def evaluation_iso (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (b.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T D.equivalence n :=
  NatIso.ofComponents (fun M ↦ evaluation_object l E b T D M n) (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change ((SpTowerShriek.ev l E T n).map
        ((b.realization T).functor.map f)).val.app U ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D N n U)) =
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) ≫
        ((spCoefficientEvaluation l E T D.equivalence n).map f).val.app U
    exact transport_morphism
      (eq_of_heq (evaluation_sections l E b T D M n U))
      (eq_of_heq (evaluation_sections l E b T D N n U)) _ _
      (evaluation_maps l E b T D f n U))

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem finite_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, a', b', ht⟩ := h
  refine ⟨⟨a, b, hab, fun i hi ↦
    (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩, ?_,
    a', b', tor_of_iso T A e ht⟩
  intro i
  apply (Scheme.proEtaleModuleRestriction_constructible_iff T A _).mpr
  exact isConstructible_of_iso
    ((Scheme.proEtaleModuleRestriction T A).mapIso
      ((DerivedCategory.homologyFunctor _ i).mapIso e))
    ((Scheme.proEtaleModuleRestriction_constructible_iff T A _).mp (hc i))

/-- Localize the ordinary comparison fixed by sections and restrictions. -/
private def realization_evaluation (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (realization l E b T A).functor ⋙ Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T A n := by
  letI := A.hasDerived
  haveI := b.realizationAdditive T
  haveI := A.equivalenceAdditive
  haveI := A.evaluationLimits n
  haveI := A.evaluationColimits n
  haveI : (spCoefficientEvaluation l E T A.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (evaluation_iso l E b T A n)

private def evaluation_comparison (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (K : D l E T) (n : ℕ) :
    (Ev l E T n).obj K ≅ (spDerivedCoefficientEvaluation l E T A n).obj
      ((realization l E b T A).inverse.obj K) :=
  (Ev l E T n).mapIso ((realization l E b T A).counitIso.app K).symm ≪≫
    (realization_evaluation l E b T A n).app _

private theorem evaluated_constructibleTor (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (K : D l E T)
    (hK : constructibleTor l E b T A K) (n : ℕ) :
    spFiniteConstructibleTor T (R l E n) ((Ev l E T n).obj K) :=
  finite_of_iso T _ (evaluation_comparison l E b T A K n).symm (hK.1 n)

private theorem isIso_pair {A B : Type*} [Category* A] [Category* B]
    {W X : A} {Y Z : B} (f : W ⟶ X) (g : Y ⟶ Z) [IsIso f] [IsIso g] :
    IsIso (Prod.mkHom f g) :=
  (CategoryTheory.isIso_prod_iff A B).mpr ⟨inferInstance, inferInstance⟩


private theorem isIso_of_iso_suffixes {A : Type*} [Category* A]
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    [IsIso g] [IsIso h] (hi : IsIso (f ≫ g ≫ h)) : IsIso f := by
  exact IsIso.of_isIso_comp_right f (g ≫ h)

private def equivalence_counit_transport {A B : Type*} [Category* A] [Category* B]
    (e : A ≌ B) (F : A ⥤ B) (h : e.functor = F) (K : B) :
    F.obj (e.inverse.obj K) ≅ K := by
  cases h
  exact e.counitIso.app K


attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers

attribute [local irreducible] HasProEtaleTorAmplitude ProEtale.projectionMapOfCompactification
  ProEtale.derivedTensor
  CategoryTheory.Functor.leftDerivedFunctor ProEtale.upperStar
attribute [local instance 100000] SheafOfModules.instAbelian
attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem fixed_constructible
    (A : Type u) [CommRing A] [Finite A] (W : Scheme.{u})
    (K : proEtaleDerivedCategory W A)
    (hc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf W A
      ((DerivedCategory.homologyFunctor _ i).obj K))
    (a b : ℤ) (hab : a ≤ b)
    (hv : ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W
      ((sfIntrinsicDerivedEquivalence W A).inverse.obj K) := by
  obtain ⟨M, ⟨eM⟩⟩ := ((finiteRing_constructibleDerived_origin W A).2.2.1 K).mpr
    ⟨hc, a, b, hab, hv⟩
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W
  let G := ProEtale.finiteCoefficientIntrinsicRealization W A
  let R := sfIntrinsicDerivedEquivalence W A
  let ecomp : ProEtale.finiteCoefficientIntrinsicDerivedComparison W A ≅
      F.mapDerivedCategory.{u + 1, u + 1} ⋙ R.functor :=
    Functor.mapDerivedCategoryCompIso F G
  let e : F.mapDerivedCategory.{u + 1, u + 1}.obj M.obj ≅ R.inverse.obj K :=
    R.unitIso.app _ ≪≫ R.inverse.mapIso
      (ecomp.symm.app M.obj ≪≫ eM)
  have hb : DerivedCategory.TStructure.t.bounded M.obj := by
    obtain ⟨r, s, _, hz⟩ := M.property.2
    exact ⟨⟨r, (DerivedCategory.isGE_iff _ r).mpr (fun i hi ↦ hz i (.inl hi))⟩,
      ⟨s, (DerivedCategory.isLE_iff _ s).mpr (fun i hi ↦ hz i (.inr hi))⟩⟩
  apply (ProEtale.DerivedCategory.boundedConstructible_iff _ _ _).mpr
  exact ⟨M.obj, ⟨hb, fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (M.property.1 i)⟩, ⟨e⟩⟩


private theorem intrinsic_derived_functor (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).functor =
      (sfIntrinsicModuleEquivalence T A).functor.mapDerivedCategory := by
  unfold sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
  rfl



private theorem intrinsic_derived_inverse (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).inverse =
      (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory := by
  unfold sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
  rfl

attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem fixed_tor
    (A : Type u) [CommRing A] [Finite A] (W : Scheme.{u})
    (K : proEtaleDerivedCategory W A) (a b : ℤ)
    (ht : HasProEtaleTorAmplitude W A K a b) :
    ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W a b
      ((sfIntrinsicDerivedEquivalence W A).inverse.obj K) := by
  rw [intrinsic_derived_inverse]
  let R := sfIntrinsicModuleEquivalence W A
  have hab : a ≤ b := by
    unfold HasProEtaleTorAmplitude at ht
    exact ht.1
  have ht' : HasProEtaleTorAmplitude W A
      (R.functor.mapDerivedCategory.obj (R.inverse.mapDerivedCategory.obj K)) a b := by
    unfold HasProEtaleTorAmplitude at ht ⊢
    refine ⟨ht.1, ?_⟩
    intro B P hB v hv hP M i hi
    exact ht.2 B P (hB.map (fun z ↦ z ≪≫ R.mapDerivedCategory.counitIso.app K))
      v hv hP M i hi
  have h := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    A W a b hab (R.inverse.mapDerivedCategory.obj K)).mp
      (by simpa only [R, sfIntrinsicModuleEquivalence, Functor.asEquivalence_functor] using ht')
  exact h

private theorem projection_iso_of_property
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A))
    (h : ProEtale.HasProjectionFormulaOfCompactification A c K L) :
    IsIso (((ProEtale.projectionMapOfCompactification A c).app K).app L) := h


attribute [local irreducible] ProEtale.HasProjectionFormulaOfCompactification

set_option linter.style.haveILetI false in
private theorem map_isIso_of_proof
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N : C} (f : M ⟶ N) (hf : IsIso f) : IsIso (F.map f) := by
  letI := hf
  exact F.map_isIso f


-- Reuse congruence proofs at repeated instance boundaries. This constructs ordinary
-- equality proofs; the kernel checks the resulting projection-coordinate comparison.
private theorem ulift_ring_coherence (A : Type u) [CommRing A] :
    (ULift.ring : Ring (ULift.{u + 1, u} A)) = ULift.commRing.toRing := by
  rfl

private theorem module_braided_coherence (A : Type u) [CommRing A] :
    (ModuleCat.MonoidalCategory.instBraidedCategory : BraidedCategory (ModuleCat.{u} A)) =
      ModuleCat.MonoidalCategory.symmetricCategory.toBraidedCategory := by
  rfl

private meta def projectionHead (fuel : Nat) (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e := e.consumeMData
    let names := [``comparisonFiniteProjection,
      ``SheafOfModules.OpenTensorNormalization.FiniteD,
      ``SheafOfModules.OpenTensorNormalization.FiniteModules,
      ``SheafOfModules.OpenTensorNormalization.finiteTensor,
      ``ProEtale.rightDerivedLowerShriekOfCompactification,
      ``ProEtale.derivedTensorRightDerivedLowerShriek,
      ``ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
      ``CategoryTheory.Functor.uncurry, ``CategoryTheory.Functor.comp,
      ``CategoryTheory.Functor.postcompose₂, ``CategoryTheory.Functor.whiskeringLeft₂,
      ``CategoryTheory.Functor.whiskeringLeft, ``CategoryTheory.Functor.whiskeringRight,
      ``CategoryTheory.Functor.id, ``id]
    if names.any e.getAppFn.isConstOf then
      if let some e' ← Lean.Meta.unfoldDefinition? e then
        return ← projectionHead fuel e'
    let objData? := match e.getAppFn with
      | .const ``CategoryTheory.Functor.obj _ =>
        let args := e.getAppArgs
        if args.size ≥ 2 then some (args[args.size - 2]!, args.back!) else none
      | .proj ``CategoryTheory.Functor 0 F =>
        if e.getAppNumArgs == 1 then some (F, e.getAppArgs[0]!) else none
      | _ => none
    if let some (F, x) := objData? then
      let F' ← projectionHead fuel F
      if F' != F then
        let e' ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[F', x]
        return ← projectionHead fuel
          (← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e'))
    match e with
    | .letE .. => return ← projectionHead fuel (← Lean.Meta.whnf e)
    | _ =>
      let e' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e)
      if e' != e then return ← projectionHead fuel e'
      match e.getAppFn with
      | .proj ``CategoryTheory.NatTrans 0 z =>
        return Lean.mkAppN (← Lean.Meta.mkAppM ``CategoryTheory.NatTrans.app #[z]) e.getAppArgs
      | .proj ``CategoryTheory.Functor 0 z =>
        return Lean.mkAppN (← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[z]) e.getAppArgs
      | .proj ``CategoryTheory.Functor 1 z =>
        return Lean.mkAppN (← Lean.Meta.mkAppM ``CategoryTheory.Functor.map #[z]) e.getAppArgs
      | _ => return e

private meta def projectionCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "coordinate congruence recursion limit"
  | fuel + 1 =>
    let (_, g) ← g.intros
    g.withContext do
      let t ← Lean.instantiateMVars (← g.getType)
      try
        g.assumption
        return
      catch _ => pure ()
      let entries ← cache.get
      if let some pf := entries[t]? then
        let ctx ← Lean.getLCtx
        let missing := pf.find? fun e => match e with
          | .fvar id => !(ctx.contains id)
          | _ => false
        if missing.isNone then
          g.assign pf
          return
      let (a, b) ← if let some (_, a, b) := t.eq? then pure (a, b)
        else if let some (_, a, _, b) := t.heq? then pure (a, b)
        else throwError "unexpected congruence goal {t}"
      if a == b then
        if t.isHEq then g.hrefl else g.refl
        return
      let a ← projectionHead 60 a
      let b ← projectionHead 60 b
      let t' ← if t.isHEq then Lean.Meta.mkHEq a b else Lean.Meta.mkEq a b
      let g ← g.change t'
      let coherence? := if a.getAppFn.isConstOf ``ULift.ring then
        some ``ulift_ring_coherence
        else if a.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory then
          some ``module_braided_coherence
        else none
      if let some lemmaName := coherence? then
        let h ← Lean.Meta.mkAppOptM lemmaName #[some (a.getAppArgs[0]!), none]
        let h ← if t.isHEq then Lean.Meta.mkAppM ``heq_of_eq #[h] else pure h
        let gs ← g.apply h { synthAssignedInstances := false }
        for g in gs do projectionCongr cache fuel g
        return
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else if ← g.proofIrrelHeq then pure ()
      else if t.isEq then
        let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
          { synthAssignedInstances := false }
        for g in gs do projectionCongr cache fuel g
      else if a.isLambda || b.isLambda then
        let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``Function.hfunext)
          { synthAssignedInstances := false }
        for g in gs do projectionCongr cache fuel g
      else if a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
        let f := a.getAppFn
        let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
        let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
        let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
          (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
        let gs ← g.apply (c.proof.beta #[f]) { synthAssignedInstances := false }
        for i in [:gs.length] do
          try projectionCongr cache fuel gs[i]!
          catch ex => throwError "in {a} versus {b}, goal {i}: {ex.toMessageData}"
      else
        throwError "projection coordinates have unmatched expressions: {a} / {b}"
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

set_option maxHeartbeats 1500000 in
-- The congruence proof compares dependent functor records and canonical instance arguments.
private theorem finite_projection_coordinates_heq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (L : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    HEq (IsIso (comparisonFiniteProjection l E b c n K L))
      (IsIso (((ProEtale.projectionMapOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).app K).app L)) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    projectionCongr cache 100 (← Lean.Elab.Tactic.getMainGoal)
    Lean.Elab.Tactic.replaceMainGoal []

private theorem finite_projection_generic_isIso (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (L : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hK : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X K)
    (hL : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y L)
    (a b : ℤ) (ht : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y a b L) :
    IsIso (((ProEtale.projectionMapOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app K).app L) := by
  exact projection_iso_of_property _ c K L
    (ProEtale.hasProjectionFormulaOfCompactification_of_boundedConstructible
      (ULift.{u + 1, u} A) c hK ⟨hL, a, b, ht⟩)

/-- The source finite formula in the fixed realization coordinates. -/
private theorem finite_source_projection_isIso (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (K : proEtaleDerivedCategory X (R l E n))
    (L : proEtaleDerivedCategory Y (R l E n))
    (hK : spFiniteConstructibleTor X (R l E n) K)
    (hL : spFiniteConstructibleTor Y (R l E n) L) :
    IsIso ((comparisonFiniteRealization l E b Y n).map
      (comparisonFiniteProjection l E b c n
        ((sfIntrinsicDerivedEquivalence X (R l E n)).inverse.obj K)
        ((sfIntrinsicDerivedEquivalence Y (R l E n)).inverse.obj L))) := by
  obtain ⟨r, s, hrs, hvK⟩ := hK.1
  obtain ⟨r', s', hrs', hvL⟩ := hL.1
  obtain ⟨v, w, htor⟩ := hL.2.2
  have hbcK := fixed_constructible (R l E n) X K hK.2.1 r s hrs hvK
  have hbcL := fixed_constructible (R l E n) Y L hL.2.1 r' s' hrs' hvL
  have htL := fixed_tor (R l E n) Y L v w htor
  have h := finite_projection_generic_isIso (R l E n) c _ _ hbcK hbcL v w htL
  have he := finite_projection_coordinates_heq l E b c n
    ((sfIntrinsicDerivedEquivalence X (R l E n)).inverse.obj K)
    ((sfIntrinsicDerivedEquivalence Y (R l E n)).inverse.obj L)
  exact map_isIso_of_proof (comparisonFiniteRealization l E b Y n) _
    ((eq_of_heq he).mpr h)



/-- Use the existing transport theorem with origins provided by constructibility. -/
private theorem finite_projection_on_evaluations (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) (a : StrictFiniteCoordinates l E b)
    (hcomp : StrictFiniteProjectionComparisons l E b o levels a)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (n : ℕ) (K : D l E X) (L : D l E Y)
    (hK : spFiniteConstructibleTor X (R l E n) ((Ev l E X n).obj K))
    (hL : spFiniteConstructibleTor Y (R l E n) ((Ev l E Y n).obj L)) :
    IsIso (comparisonLevelProjection l E b o levels c n
      ((Ev l E X n).obj K) ((Ev l E Y n).obj L)) := by
  obtain ⟨r, s, hrs, hvK⟩ := hK.1
  obtain ⟨r', s', hrs', hvL⟩ := hL.1
  have hbcK := fixed_constructible (R l E n) X _ hK.2.1 r s hrs hvK
  have hbcL := fixed_constructible (R l E n) Y _ hL.2.1 r' s' hrs' hvL
  obtain ⟨V, hV, ⟨eV⟩⟩ := hbcK.plusEtaleOrigin
  obtain ⟨W, hW, ⟨eW⟩⟩ := hbcL.plusEtaleOrigin
  let wK : Origin l E b X n K := {
    level := ⟨_, hbcK.bounded.1⟩
    realization := equivalence_counit_transport
      (sfIntrinsicDerivedEquivalence X (R l E n))
      ((sfIntrinsicModuleEquivalence X (R l E n)).functor.mapDerivedCategory)
      (intrinsic_derived_functor X (R l E n)) ((Ev l E X n).obj K)
    witness := ⟨⟨V, hV⟩, eV⟩ }
  let wL : Origin l E b Y n L := {
    level := ⟨_, hbcL.bounded.1⟩
    realization := equivalence_counit_transport
      (sfIntrinsicDerivedEquivalence Y (R l E n))
      ((sfIntrinsicModuleEquivalence Y (R l E n)).functor.mapDerivedCategory)
      (intrinsic_derived_functor Y (R l E n)) ((Ev l E Y n).obj L)
    witness := ⟨⟨W, hW⟩, eW⟩ }
  exact finite_level_projection_transport_isIso l E b o levels a hcomp f c n K L wK wL
    (finite_source_projection_isIso l E b c n _ _ hK hL)


/-- The proper, open, and compact-support projection arrows are isomorphisms.
Source: finite proper projection, the open unit/counit triangle, and tower
conservativity in paragraph (3),
`lem-sp-tower-compact-support-projection-formula`.
(blueprint: lem-sp-tower-compact-support-projection-isos) -/
theorem tower_compact_support_proper_projection_isIso
    (b : Base l E) (o : Operations l E b)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpCoefficientTowersAbelian l E X.left)
    (AY : SpCoefficientTowersAbelian l E Y.left)
    (C : D l E X.left) (B : D l E Y.left)
    (_hC : constructibleTor l E b X.left AX C)
    (_hB : constructibleTor l E b Y.left AY B) :
    IsIso (properMap l E b o c C B) := by
  classical
  have : IsSeparated (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  obtain ⟨x, levels, hwords⟩ := strictOpenWordEvaluation l E b o
    (strict_system_comparisons l E b o)
  obtain ⟨a, _, hcomp⟩ := strictFiniteWordIdentification l E b o levels
  have hfinite (n : ℕ) : IsIso
      (comparisonLevelProjection l E b o levels c n
        ((Ev l E X.left n).obj C) ((Ev l E Y.left n).obj B)) :=
    finite_projection_on_evaluations l E b o levels a hcomp c n C B
      (evaluated_constructibleTor l E b X.left AX C _hC n)
      (evaluated_constructibleTor l E b Y.left AY B _hB n)
  have hp : IsIso (SpTowerShriek.projection l E b o c C B) := by
    apply (b.calculus Y.left).detects
    intro n
    have := hfinite n
    have he := hwords.2.1 c n C B
    have hpair : IsIso (Prod.mkHom ((Fcomparison l E b o c n).hom.app C)
        (𝟙 ((Ev l E Y.left n).obj B))) := isIso_pair _ _
    have hright : IsIso
        (((b.calculus Y.left).tensorEvaluation n).hom.app ((F l E b o c).obj C, B) ≫
          (comparisonLevelTensor l E b Y.left n).map
            (Prod.mkHom ((Fcomparison l E b o c n).hom.app C) (𝟙 _)) ≫
          comparisonLevelProjection l E b o levels c n
            ((Ev l E X.left n).obj C) ((Ev l E Y.left n).obj B)) := by
      infer_instance
    rw [← he] at hright
    have htargetPair : IsIso (Prod.mkHom
        (𝟙 ((Ev l E X.left n).obj C))
        (((o.geometry f.left).pullEvaluation n).hom.app B)) := isIso_pair _ _
    exact isIso_of_iso_suffixes _ _ _ hright
  let w := (push l E b (o.geometry c.g)).map
    ((o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).hom ≫
      (openD l E b (o.openOp c.i)).map ((tensor l E b X.left).map
        (Prod.mkHom (𝟙 C) ((o.comp c.i c.g).hom.app B ≫
          (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom.app B))))
  have hpair : IsIso (Prod.mkHom (𝟙 C)
      ((o.comp c.i c.g).hom.app B ≫
        (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom.app B)) :=
    isIso_pair _ _
  have hw : IsIso w := by
    dsimp only [w]
    infer_instance
  change IsIso (properMap l E b o c C B ≫ w) at hp
  exact IsIso.of_isIso_comp_right _ w

end AlgebraicGeometry.ProEtale.SpTowerProjection
