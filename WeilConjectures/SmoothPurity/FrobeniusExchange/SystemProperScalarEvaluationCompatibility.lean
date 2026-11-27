/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation
import all WeilConjectures.SixFunctors.FrobeniusExchange.SystemScalarPullbackGeneralMate
import all WeilConjectures.SixFunctors.FrobeniusExchange.SystemOpenScalarPullbackMate
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.Tactic.ExactByKernel

/-! # The scalar/pullback compatibility square used by proper evaluation

## Implementation details

This square is stated separately so that the mate calculation in
`systemDirectScalar_finiteEvaluation` is a formal consequence of
`SemilinearSections.evaluation_mate`. It is proved on a common flat-term K-flat model using
the universal scalar counits and the K-injective normalization of
`sfDerivedImageRestriction`, then transported by naturality to all derived systems.

## References

* W. Zheng, Construction 4.1 and Lemma 4.10
* Stacks Project, Tags 06YY, 07A6 and 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar
open WeilConjectures.SemilinearSections

section EvaluationMate

universe c v r

/-- The level evaluation comparison of normalized semilinear scalar systems is the inverse
mate of restriction evaluation, as forced by its transpose field. -/
private theorem scalarSystems_evaluation_inv_eq_restrictionMate {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (F : ℕ → Sheaf J CommRingCat.{max c v r}) (σ : ∀ n : ℕ, F (n + 1) ⟶ F n)
    (α : ∀ n : ℕ, B n ⟶ F n) (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n)
    (d : SemilinearSections.ScalarSystems.{c, v, r} J B τ F σ α hα) (n : ℕ) :
    (d.evaluation n).inv = ((mateEquiv d.scalar.adjunction (d.levels n).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (SemilinearSections.restrictionEvaluation.{c, v, max c v r}
          J B τ F σ α hα n).hom)) := by
  ext M
  apply ((d.levels n).adjunction.homEquiv _ _).injective
  have h := d.transpose_evaluation n M _ (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at h
  erw [← h, Adjunction.homEquiv_unit]
  exact unit_mateEquiv_symm _ _ _ M

end EvaluationMate

/-- Conjugating an evaluation comparison by adjoint-uniqueness isomorphisms replaces the
adjunctions in its inverse-mate description. -/
private theorem isoInv_leftAdjointUniq_eq_inverseMate {C D C' D' : Type*} [Category C]
    [Category D] [Category C'] [Category D'] {L L' : C ⥤ D} {R : D ⥤ C} {l l' : C' ⥤ D'}
    {r : D' ⥤ C'} {G : C ⥤ C'} {H : D ⥤ D'} (a : L ⊣ R) (b : L' ⊣ R) (c : l ⊣ r)
    (c' : l' ⊣ r) (ev : L' ⋙ H ≅ G ⋙ l) (w : TwoSquare R H G r)
    (hev : ev.inv = ((mateEquiv b c).symm w)) :
    (Functor.isoWhiskerRight (a.leftAdjointUniq b) H ≪≫ ev ≪≫
      Functor.isoWhiskerLeft G (c.leftAdjointUniq c')).inv =
      ((mateEquiv a c').symm w) := by
  have hw : (mateEquiv a c').symm w = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G (c'.leftAdjointUniq c).hom ≫ ((mateEquiv b c).symm w) ≫
        Functor.whiskerRight (a.leftAdjointUniq b).inv H) := by
    apply (mateEquiv a c').injective
    rw [Equiv.apply_symm_apply, mateEquiv_leftAdjointUniq, Equiv.apply_symm_apply]
  rw [hw, ← hev]
  ext X
  simp [Adjunction.leftAdjointUniq_inv_app]

/-- Inverse mates along heterogeneously equal adjunctions whose right adjoints differ by
an equality of parameters. -/
private theorem inverseMate_heq_of_eq {X : Sort*} {C D C' D' : Type*} [Category C]
    [Category D] [Category C'] [Category D'] {L : C ⥤ D} (Rf : X → (D ⥤ C)) {l : C' ⥤ D'}
    {r : D' ⥤ C'} {G : C ⥤ C'} {H : D ⥤ D'} {φ₁ φ₂ : X} (h : φ₁ = φ₂) (a : L ⊣ Rf φ₁)
    (b : L ⊣ Rf φ₂) (hab : HEq a b) (c : l ⊣ r) (w : TwoSquare (Rf φ₁) H G r) :
    ∃ w' : TwoSquare (Rf φ₂) H G r, HEq w' w ∧
      (mateEquiv a c).symm w = (mateEquiv b c).symm w' := by
  subst h
  obtain rfl := eq_of_heq hab
  exact ⟨w, HEq.rfl, rfl⟩

/-- A cast by `Eq.mpr` is heterogeneously equal to its argument. -/
private theorem eq_mpr_heq.{w} {α β : Sort w} (h : α = β) (b : β) : HEq (Eq.mpr h b) b := by
  subst h
  rfl

section FiniteEvaluationMate

-- the evaluation comparison unfolds the chosen scalar systems
/-- The normalized finite evaluation of system scalar extension is the inverse mate of
restriction evaluation along the normalized system and finite scalar adjunctions. -/
private theorem finiteEvaluation_inv_eq_restrictionMate (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) (n : ℕ) :
    ∃ ρ : TwoSquare (SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι W))
        (coefficientSequenceDerivedEvaluation l L W n)
        (coefficientSequenceDerivedEvaluation l E W n)
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) W)),
      HEq ρ (SemilinearSections.restrictionEvaluation (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (scalarQuotient_compatible l E L ι W) n).hom ∧
      (systemScalarFiniteEvaluation l E L ι W n).inv =
        ((mateEquiv (finiteEvaluationSystemScalarAdjunction l E L ι W)
          (pbcDerivedScalarAdjunction
            (scalarRingMap (integralScalarQuotientMap l E L ι n) W))).symm
          ρ) := by
  obtain ⟨w', hw', he⟩ := inverseMate_heq_of_eq (fun φ ↦ SemilinearSections.resD φ)
    (scalarSystemMap_eq l E L ι W)
    (by rw [scalarSystemMap_eq]; exact finiteEvaluationSystemScalarAdjunction l E L ι W)
    (finiteEvaluationSystemScalarAdjunction l E L ι W) (eq_mpr_heq _ _)
    (pbcDerivedScalarAdjunction (scalarRingMap (integralScalarQuotientMap l E L ι n) W))
    (TwoSquare.mk _ _ _ _ (SemilinearSections.restrictionEvaluation (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W) (scalarQuotient_compatible l E L ι W) n).hom)
  exact ⟨w', hw', (isoInv_leftAdjointUniq_eq_inverseMate _ _ _ _ _ _
    (scalarSystems_evaluation_inv_eq_restrictionMate _ _ _ _ _ _ _ _ n)).trans he⟩

end FiniteEvaluationMate

/-- The evaluated scalar/pullback cube required by the mate-pasting proof of the proper
scalar evaluation formula: the specified double mate of the normalized direct-image
restriction comparison agrees with the finite tensor/pullback square. -/
theorem systemProperScalarEvaluation_compatibility
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    let levelE := (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction
    let levelL := (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategoryRightDerivedAdjunction
    let φ := integralScalarQuotientMap l E L ι n
    let scalarMate := ((mateEquiv
      (pbcDerivedScalarAdjunction (scalarRingMap φ X))
      (pbcDerivedScalarAdjunction (scalarRingMap φ Y))).symm
      (TwoSquare.mk _ _ _ _ (sfDerivedImageRestriction f φ).hom))
    let a := (mateEquiv levelE levelL).symm scalarMate
    ∀ A : coefficientSequenceDerived l E Y,
      (coefficientSequenceDerivedEvaluation l L X n).map
          ((integralComparisonSystemScalarPullback l E L ι f).inv.app A) ≫
        (systemScalarFiniteEvaluation l E L ι X n).hom.app
          ((integralComparisonDerivedSequencePullback l E f).obj A) ≫
        (pbcDerivedExtend
            (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
          ((systemPullEvaluation l E f n).inv.app A) =
      (systemPullEvaluation l L f n).inv.app
          ((integralComparisonDerivedSequenceScalar l E L ι Y).obj A) ≫
        (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l L (n + 1)) f).map
          ((systemScalarFiniteEvaluation l E L ι Y n).hom.app A) ≫
        a.app ((coefficientSequenceDerivedEvaluation l E Y n).obj A) := by
  intro levelE levelL φ scalarMate a A
  have := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  obtain ⟨ρX, hρX, hβX⟩ := finiteEvaluation_inv_eq_restrictionMate l E L ι X n
  obtain ⟨ρY, hρY, hβY⟩ := finiteEvaluation_inv_eq_restrictionMate l E L ι Y n
  obtain ⟨ρX₀, hρX₀, hΔX⟩ := systemRestrictionEvaluation_isDerivedSquareOf l E L ι X n ρX hρX
  obtain ⟨ρY₀, hρY₀, hΔY⟩ := systemRestrictionEvaluation_isDerivedSquareOf l E L ι Y n ρY hρY
  obtain ⟨Qd, hQd⟩ := Functor.exists_isDerivedSquareOf (sequenceRestrictionPullbackInv l E L ι f)
  -- the two presentations of the evaluated direct image are compared by the kernel
  have hord := ordinaryDirectRestrictionEvaluation_cube l E L ι f n
    (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).hom (fun M U y ↦ by
      exact_by_kernel eqToIso_hom_app_val_app_heq l E (systemDirectEvaluationOrdinary_eq l E f n)
        M U y)
    (eqToIso (systemDirectEvaluationOrdinary_eq l L f n)).hom (fun M U y ↦ by
      exact_by_kernel eqToIso_hom_app_val_app_heq l L (systemDirectEvaluationOrdinary_eq l L f n)
        M U y)
    ρY₀ hρY₀ ρX₀ hρX₀
  have hcube₀ := leftMate_cube_of_rightCube
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L f))
    (sfIntrinsicConstantModuleAdjunction f (Padic.coefficientExtensionRing l E (n + 1)))
    (sfIntrinsicConstantModuleAdjunction f (Padic.coefficientExtensionRing l L (n + 1)))
    (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).hom
    (eqToIso (systemDirectEvaluationOrdinary_eq l L f n)).hom
    (sequenceScalarPullbackRight l E L ι f).inv
    (proEtaleCoefficientDirectImageComparison f φ).hom ρY₀ ρX₀ (by exact_by_kernel hord)
  have := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
  have := sfIntrinsicPullback_preservesFiniteLimits (Padic.coefficientExtensionRing l E (n + 1)) f
  have := sfIntrinsicPullback_preservesFiniteColimits (Padic.coefficientExtensionRing l E (n + 1)) f
  have := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l L (n + 1)) f
  have := sfIntrinsicPullback_preservesFiniteLimits (Padic.coefficientExtensionRing l L (n + 1)) f
  have := sfIntrinsicPullback_preservesFiniteColimits (Padic.coefficientExtensionRing l L (n + 1)) f
  have := coefficientSequenceEvaluation_additiveInstance l E X n
  have := coefficientSequenceEvaluation_additiveInstance l E Y n
  have := coefficientSequenceEvaluation_additiveInstance l L X n
  have := coefficientSequenceEvaluation_additiveInstance l L Y n
  have := coefficientSequenceEvaluation_limits l E X n
  have := coefficientSequenceEvaluation_limits l E Y n
  have := coefficientSequenceEvaluation_limits l L X n
  have := coefficientSequenceEvaluation_limits l L Y n
  have := coefficientSequenceEvaluation_colimits l E X n
  have := coefficientSequenceEvaluation_colimits l E Y n
  have := coefficientSequenceEvaluation_colimits l L X n
  have := coefficientSequenceEvaluation_colimits l L Y n
  have hΔE : Functor.IsDerivedSquareOf (systemPullEvaluationOrdinaryInv l E f n)
      (systemPullEvaluation l E f n).hom := by
    exact_by_kernel Functor.isDerivedSquareOf_mapDerivedCategorySquareIso
      (@asIso _ _ _ _ (systemPullEvaluationOrdinaryInv l E f n)
        (systemPullEvaluationOrdinaryInv_isIso l E f n))
  have hΔL : Functor.IsDerivedSquareOf (systemPullEvaluationOrdinaryInv l L f n)
      (systemPullEvaluation l L f n).hom := by
    exact_by_kernel Functor.isDerivedSquareOf_mapDerivedCategorySquareIso
      (@asIso _ _ _ _ (systemPullEvaluationOrdinaryInv l L f n)
        (systemPullEvaluationOrdinaryInv_isIso l L f n))
  have hcube := Functor.derivedCube_of_isDerivedSquareOf
    (δE := systemPullEvaluationOrdinaryInv l E f n) (δL := systemPullEvaluationOrdinaryInv l L f n)
    (Q := sequenceRestrictionPullbackInv l E L ι f) (by exact_by_kernel hcube₀) hΔE hΔL hQd
    (sfDerivedImageRestriction_inverseMate_isDerivedSquareOf φ f) hΔY hΔX
  exact scalarPullback_evaluation_cube levelE levelL
    (finiteEvaluationSystemScalarAdjunction l E L ι Y)
    (finiteEvaluationSystemScalarAdjunction l E L ι X)
    (pbcDerivedScalarAdjunction (scalarRingMap φ Y))
    (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (coefficientSequenceDerivedEvaluation l E Y n) (coefficientSequenceDerivedEvaluation l L Y n)
    (coefficientSequenceDerivedEvaluation l E X n) (coefficientSequenceDerivedEvaluation l L X n)
    (integralComparisonSystemScalarPullback l E L ι f) Qd
    (systemScalarPullback_hom_eq_finiteMate_general l E L ι f Qd hQd)
    (systemScalarFiniteEvaluation l E L ι X n) ρX hβX
    (systemScalarFiniteEvaluation l E L ι Y n) ρY hβY
    (systemPullEvaluation l E f n) (systemPullEvaluation l L f n)
    (sfDerivedImageRestriction f φ) hcube a rfl A

end WeilConjectures.FrobeniusExchange
