/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionCompactificationData
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionRefinementSquare
import WeilConjectures.SixFunctors.Integral.IntegralStageProjectionStructuralIdentities
import WeilConjectures.SixFunctors.Rational.RationalProjectionComparisonEquations
import WeilConjectures.SixFunctors.Common.CommonProjectionComparisonEquations
import WeilConjectures.Compactification.CommonRefinement

/-! # Localization and common-stage transport of the projection refinement square

Source: current blueprint, prop-sf-pf-coherence.proof.md, coefficient transport of
compactification independence (blueprint: lem-sf-field-projection-refinement-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification

/-- Two commuting refinement squares give the square for the common-refinement composite.
Source: compactification-independence calculation, step 6
(blueprint: lem-fix-projection-compactification-comparison). -/
private theorem commonRefinementSquare
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a a₁ a₂ : A} {b b₁ b₂ : B}
    (t₁ : a ≅ a₁) (t₂ : a ≅ a₂) (s₁ : b ≅ b₁) (s₂ : b ≅ b₂)
    (p : F.obj a ⟶ b) (p₁ : F.obj a₁ ⟶ b₁) (p₂ : F.obj a₂ ⟶ b₂)
    (h₁ : p ≫ s₁.hom = F.map t₁.hom ≫ p₁)
    (h₂ : p ≫ s₂.hom = F.map t₂.hom ≫ p₂) :
    p₁ ≫ (s₁.symm ≪≫ s₂).hom = F.map (t₁.symm ≪≫ t₂).hom ≫ p₂ := by
  have hi : p₁ ≫ s₁.inv = F.map t₁.inv ≫ p := by
    apply (cancel_epi (F.map t₁.hom)).1
    rw [← Category.assoc, ← h₁]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← Functor.map_comp_assoc, Iso.hom_inv_id]
    rw [F.map_id, Category.id_comp]
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] using
    calc
      p₁ ≫ s₁.inv ≫ s₂.hom = (p₁ ≫ s₁.inv) ≫ s₂.hom := by simp
      _ = (F.map t₁.inv ≫ p) ≫ s₂.hom := by rw [hi]
      _ = F.map t₁.inv ≫ F.map t₂.hom ≫ p₂ := by rw [Category.assoc, h₂]

/-- The comparison cocycle promotes the local refinement square to any pair of
compactifications. Source: compactification-independence calculation, step 6
(blueprint: lem-fix-projection-compactification-comparison). -/
private theorem higherComparison
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ Y, ObjectProperty (B Y)) (h : refinementLaw S T A P) :
    higherLaw S T A P := by
  intro X Y f _ _ _ c₁ c₂ K L hL
  obtain ⟨d, ⟨r₁⟩, ⟨r₂⟩⟩ := Compactification.exists_common_refinement c₁ c₂
  have hcomp : S.comparison f c₁ c₂ =
      (S.comparison f d c₁).symm ≪≫ S.comparison f d c₂ := by
    rw [S.comparison_trans f d c₁ c₂]
    simp
  have heq := commonRefinementSquare ((T Y).flip.obj L)
    ((S.comparison f d c₁).app K) ((S.comparison f d c₂).app K)
    ((S.comparison f d c₁).app (((T X).obj K).obj ((S.pull f).obj L)))
    ((S.comparison f d c₂).app (((T X).obj K).obj ((S.pull f).obj L)))
    ((A (identitySquare f d)).projectionComponent K L)
    ((A (identitySquare f c₁)).projectionComponent K L)
    ((A (identitySquare f c₂)).projectionComponent K L)
    (h f d c₁ r₁ K L hL) (h f d c₂ r₂ K L hL)
  simpa only [hcomp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.flip_obj_map, Functor.flip_obj_obj, SixFunctorCompactifiedSquare.compactification,
    identitySquare, Iso.app_hom, Iso.app_inv] using heq

/-- Assemble the integral comparison equation with the three existing structural equations.
Source: compactification-independence and coherence sentences of the projection proof
(blueprint: lem-sf-field-projection-refinement-square). -/
private theorem integralCoherence
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k)) :
    CompactSupportProjectionCoherence S.higher.integral S.higher.integralTensor
      S.higher.integralExchange S.integralFiniteTorDomain := by
  obtain ⟨hcomp, hpent, hproper⟩ := integralStageProjection_structuralIdentities S
  refine ⟨?_, hcomp, hpent, hproper⟩
  intro X Y f _ _ _ c d K L hL
  have h : higherLaw S.higher.integral S.higher.integralTensor S.higher.integralExchange
      S.integralFiniteTorDomain :=
    higherComparison _ _ _ _ (integralRefinementProjection D C E n hn S hl)
  exact (h f c d K L hL).symm

/-- A single refinement projection square at rational and algebraically closed
coefficients. These are the images of the integral square, with all coefficients
and morphisms represented at a common finite field when necessary.

Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence;
lem-fix-projection-compactification-comparison, proof step 9.
(blueprint: lem-sf-field-projection-refinement-square).

Proof: represent each rational constructible input by an integral lattice in the
recorded scalar localization. Integral constructibility over the DVR gives the
uniform finite-reduction Tor interval needed by integralRefinementProjection.
Apply scalar localization to that refinement square. The coefficient comparison
preserves compactification comparisons and the exchange/projection composites;
its tensor comparisons identify both endpoints. Naturality transports the square
along the chosen input presentations. For a localized morphism represented with a
scalar denominator, linearity multiplies both routes by the same scalar inverse,
so the square holds also for those morphisms. At the algebraically closed stage,
represent the two inputs and the finitely many structure maps at one common finite
coefficient field. Use the rational square for that coefficient stage, then its
inclusion in the Hom colimit. The scalar identity and cocycle equations carry the
tensor, pullback, adjunction and comparison factors to the prescribed factors after
any field enlargement; hence the two composites determine the same Hom class.
The argument applies to every input of the field constructible categories, including
zero and empty-scheme cases, and only refinement comparisons are inverted. -/
theorem fieldRefinementProjection
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k)) :
    refinementLaw S.higher.rational S.higher.rationalTensor S.higher.rationalExchange
      (fun _ _ ↦ True) ∧
    refinementLaw S.closure.commonStage S.closure.commonStageTensor S.closure.commonStageExchange
      (fun _ _ ↦ True) := by
  have hR := compactSupportProjectionCoherence_rational S.higher (integralCoherence S hl)
  have hE : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      CompactSupportProjectionCoherence (S.closure.coefficientStages E₀).rational
        (S.closure.coefficientStages E₀).rationalTensor
        (S.closure.coefficientStages E₀).rationalExchange (fun _ _ ↦ True) := by
    intro E₀
    let S₀ : SixFunctorOperationDatum D C
        (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E₀) 1 (by omega) :=
      { (S.coefficientIntegralNormalization E₀).finiteLevels 0 with
        higher := S.closure.coefficientStages E₀
        integralNormalization := S.coefficientIntegralNormalization E₀
        closure := S.closure
        coefficientIntegralNormalization := S.coefficientIntegralNormalization
        commonStageCoherence := S.commonStageCoherence }
    exact compactSupportProjectionCoherence_rational S₀.higher (integralCoherence S₀ hl)
  have hC := compactSupportProjectionCoherence_common S.closure hE
  constructor
  · intro X Y f _ _ _ c d _r K L hL
    exact (hR.compactification f c d K L hL).symm
  · intro X Y f _ _ _ c d _r K L hL
    exact (hC.compactification f c d K L hL).symm

end WeilConjectures.FixProjectionCompactification
