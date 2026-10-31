/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemCanonicalBridge
import WeilConjectures.AlgebraicGeometry.SfDirectImageTransitionPresentation
import all WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all WeilConjectures.AlgebraicGeometry.CompactSupportInputTowerCompatibility
import all WeilConjectures.SixFunctors.IntegralPullEvaluationQuotientSquare
import all WeilConjectures.SixFunctors.IntegralPullEvaluationDirectTransitionSquare

/-! # Finite direct-image transition transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section Transport
universe a b c v w
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  (F : A ⥤ C) (G : B ⥤ D) [F.Additive] [G.Additive]
  (S S₀ : A ⥤ B) (T T₀ : C ⥤ D)
  [S.Additive] [S₀.Additive] [T.Additive] [T₀.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits S₀] [PreservesFiniteColimits S₀]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits T₀] [PreservesFiniteColimits T₀]

private theorem transportNormalization (hS : S = S₀) (hT : T = T₀)
    (a : S ⋙ G ≅ F ⋙ T) (a₀ : S₀ ⋙ G ≅ F ⋙ T₀) (ha : HEq a a₀)
    (b : S.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      F.rightDerivedFunctor ⋙ T.mapDerivedCategory)
    (b₀ : S₀.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      F.rightDerivedFunctor ⋙ T₀.mapDerivedCategory) (hb : HEq b b₀)
    (h : CompactSupportDerivedSquareNormalization F G S₀ T₀ a₀ b₀) :
    CompactSupportDerivedSquareNormalization F G S T a b := by
  subst S₀ T₀
  cases eq_of_heq ha
  cases eq_of_heq hb
  exact h

end Transport

private theorem completedComp_eq (W : Scheme.{u})
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℕ) :
    normalizedDVRResCompletedComp l E W D hl n.le_succ =
      compactSupportSystemRestrictionComp l E W n.le_succ := by
  have he := ordinaryCompletedComp_eq
    (completedIntegralCoefficientProjection l E W D hl (n + 1))
    (normalizedDVRQuotient l E W n.le_succ)
    (completedIntegralCoefficientProjection l E W D hl n)
    (limit.w (integralCoefficientSheafSystem l E W) (homOfLE n.le_succ).op)
    (coefficientRestrictionComp l E W n.le_succ)
  dsimp only [normalizedDVRResCompletedComp]
  erw [he]
  rfl

private instance finiteDirectImage_additive {X Y : Scheme.{u}} (p : X ⟶ Y) (n : ℕ) :
    (compactSupportLevelDirectImage l E p n).Additive :=
  proEtaleConstantModuleDirectImage_additive p _

attribute [local instance] normalizedDVRModuleRes_limits normalizedDVRModuleRes_colimits

private instance normalized_kInjective (W : Scheme.{u}) (n : ℕ) :
    Abelian.HasKInjectiveResolutions (normalizedDVRModules l E W n) :=
  proEtaleRingModules_hasKInjectiveResolutions W _

set_option maxHeartbeats 1600000 in
-- Transport between the concrete coefficient categories needs extra kernel heartbeats.
private theorem directNormalization (o : Operations l E) {X Y : Scheme.{u}}
    (p : X ⟶ Y) (n : ℕ) :
    CompactSupportDerivedSquareNormalization
      (compactSupportLevelDirectImage l E p n)
      (compactSupportLevelDirectImage l E p (n + 1))
      (normalizedDVRModuleRes l E X n.le_succ)
      (normalizedDVRModuleRes l E Y n.le_succ)
      (ordinary_restriction_exists l E p n).choose
      ((o.evaluation p).restrictedDirect n) := by
  let := normalizedDVRModuleRes_limits l E X n.le_succ
  let := normalizedDVRModuleRes_colimits l E X n.le_succ
  let := normalizedDVRModuleRes_limits l E Y n.le_succ
  let := normalizedDVRModuleRes_colimits l E Y n.le_succ
  apply transportNormalization
    (proEtaleConstantModuleDirectImage p (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleConstantModuleDirectImage p (Padic.coefficientExtensionRing l E (n + 2)))
    (normalizedDVRModuleRes l E X n.le_succ) _
    (normalizedDVRModuleRes l E Y n.le_succ) _
    (originRestrictionEquality l E X n).symm
    (originRestrictionEquality l E Y n).symm
    _ (proEtaleCoefficientDirectImageComparison p
      (Padic.coefficientExtensionTransition l E (n + 1))).symm
    (ordinary_restriction_exists l E p n).choose_spec
    _ (sfDerivedImageRestriction p (Padic.coefficientExtensionTransition l E (n + 1)))
    ((o.evaluation p).restrictedDirectCanonical n)
  intro J hJ I hI r hr
  exact ((proEtaleDerivedDirectImage_restrictScalars p
    (Padic.coefficientExtensionTransition l E (n + 1))).choose_spec J I r).2


set_option maxHeartbeats 1600000 in
-- Checking the section-normalized comparison unfolds the concrete sheaf functors.
@[instance_reducible] private def directData (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y) :
    CompactSupportProperImageTower.DirectData l E p where
  additive n := proEtaleConstantModuleDirectImage_additive p _
  kInjective n := proEtaleRingModules_hasKInjectiveResolutions X _
  ordinary n := (ordinary_restriction_exists l E p n).choose
  sections n M U := by
    have h := (ordinary_restriction_exists l E p n).choose_spec
    have hi := scalar_comparison_sections l E p n _ h M
    apply heq_of_eq
    funext x
    have hh := congrArg (fun f ↦ f.val.app U x)
      (((ordinary_restriction_exists l E p n).choose).hom_inv_id_app M)
    exact eq_of_heq ((hi U _).symm.trans (heq_of_eq hh))
  comparison n := (o.evaluation p).restrictedDirect n
  normalization n := directNormalization l E o p n

/-- The finite direct-image evaluation and reduction maps transport the prescribed
successor map to `sfDirectImageTransition`.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0D6E.
(blueprint: lem-sf-integral-proper-tower-transition-direct).
Proof: apply the transition equation in `Operations.DirectEvaluation` and then use
naturality of the restriction comparison on the reduction evaluation isomorphisms.
The resulting equality is transported through the exact scalar restriction. -/
theorem directImageEvaluationTransition (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y) (K : Integral l E X)
    (n : ℕ) :
    let N := (Operations.push l E o p).obj ((calculus l E X).reduction.obj K)
    (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          ((coefficientSequenceDerivedTransition l E Y n.le_succ).app N) ≫
        (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          ((normalizedDVRRes l E Y n.le_succ).map
            (((o.evaluation p).evaluation n).hom.app
              ((calculus l E X).reduction.obj K))) ≫
        (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          ((normalizedDVRRes l E Y n.le_succ).map
            ((proEtaleConstantDerivedDirectImage p
              (Padic.coefficientExtensionRing l E (n + 1))).map
              (((calculus l E X).reductionEvaluation n).hom.app K))) ≫
        (normalizedDVRResCompletedComp l E Y D hl n.le_succ).hom.app
          ((proEtaleConstantDerivedDirectImage p
            (Padic.coefficientExtensionRing l E (n + 1))).obj
            ((coefficientFiniteDerivedExtension l E X n).obj K)) =
      (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          (((o.evaluation p).evaluation (n + 1)).hom.app
            ((calculus l E X).reduction.obj K)) ≫
        (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          ((proEtaleConstantDerivedDirectImage p
            (Padic.coefficientExtensionRing l E (n + 2))).map
            (((calculus l E X).reductionEvaluation (n + 1)).hom.app K)) ≫
        sfDirectImageTransition l E p K n := by
  dsimp only
  let M := (calculus l E X).reduction.obj K
  let R := normalizedDVRResCompleted l E Y D hl (n + 1)
  let F := proEtaleConstantDerivedDirectImage p
    (Padic.coefficientExtensionRing l E (n + 2))
  have ht := (o.evaluation p).transition n M
  have hn := ((o.evaluation p).restrictedDirect n).hom.naturality
    (((calculus l E X).reductionEvaluation n).hom.app K)
  dsimp only [Functor.comp_map] at hn
  obtain ⟨p₀, hp₀, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p₀.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} := {
    p := p₀, a := 1, q := p₀, prime := hprime, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p₀).symm, k₀ := ZMod p₀,
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p₀) }
  have hl₀ : l ≠ D₀.p := by change l ≠ p₀; omega
  have hd := reconstructionFiniteTransition l E X D₀ hl₀ (calculus l E X) K n
  have he : normalizedDVRReductionTransition l E X D₀ hl₀ n.le_succ K =
      CompactSupportProperImageTower.reductionMap l E X K n := by
    unfold normalizedDVRReductionTransition CompactSupportProperImageTower.reductionMap
    rw [completedComp_eq l E X D₀ hl₀ n]
    rfl
  rw [he] at hd
  have hd' : (coefficientSequenceDerivedTransition l E X n.le_succ).app M ≫
      (normalizedDVRRes l E X n.le_succ).map
        (((calculus l E X).reductionEvaluation n).hom.app K) =
    ((calculus l E X).reductionEvaluation (n + 1)).hom.app K ≫
      CompactSupportProperImageTower.reductionMap l E X K n := by
    apply (cancel_epi (((calculus l E X).reductionEvaluation (n + 1)).inv.app K)).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [hd]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [(normalizedDVRRes l E X n.le_succ).map_id, Category.comp_id]
  dsimp [M] at hn
  have hf : (coefficientSequenceDerivedTransition l E Y n.le_succ).app
        ((Operations.push l E o p).obj M) ≫
      (normalizedDVRRes l E Y n.le_succ).map
        (((o.evaluation p).evaluation n).hom.app M) ≫
      (normalizedDVRRes l E Y n.le_succ).map
        ((proEtaleConstantDerivedDirectImage p
          (Padic.coefficientExtensionRing l E (n + 1))).map
          (((calculus l E X).reductionEvaluation n).hom.app K)) =
      ((o.evaluation p).evaluation (n + 1)).hom.app M ≫
        F.map (((calculus l E X).reductionEvaluation (n + 1)).hom.app K) ≫
        F.map (CompactSupportProperImageTower.reductionMap l E X K n) ≫
        ((o.evaluation p).restrictedDirect n).hom.app
          ((coefficientFiniteDerivedExtension l E X n).obj K) := by
    rw [← Category.assoc, ht]
    simp only [Category.assoc]
    erw [← hn]
    rw [← F.map_comp_assoc, hd']
    simp only [F.map_comp, Category.assoc]
  have hm := congrArg (fun f ↦ R.map f ≫
    (compactSupportSystemRestrictionComp l E Y n.le_succ).hom.app
      ((proEtaleConstantDerivedDirectImage p
        (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((coefficientFiniteDerivedExtension l E X n).obj K))) hf
  rw [sfDirectImageTransition_presentation l E p (directData l E o p) K n]
  rw [completedComp_eq l E Y D hl n]
  dsimp only [directData, CompactSupportProperImageTower.DirectData.comparison]
  dsimp only [R, F, M] at hm
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hm ⊢
  convert hm using 1
  dsimp only [normalizedDVRResCompleted, coefficientFiniteDerivedRestriction,
    scalarReductionDerivedRestriction, compactSupportLevelDirectImage,
    proEtaleConstantDerivedDirectImage]
  rfl

end WeilConjectures.IntegralSystemRealization
