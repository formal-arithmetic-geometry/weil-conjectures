/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionCompactificationData
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.SixFunctors.Supporting.ExchangeFunctoriality
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites

import WeilConjectures.SixFunctors.FixProjectionCompactification.FiniteProjectionCompactificationSquare
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionRefinementSquare
import WeilConjectures.SixFunctors.FixProjectionCompactification.FieldProjectionRefinementSquare
import WeilConjectures.Compactification.CommonRefinement

/-!
# Projection transformations and compactification comparison

Source: main-20261015 blueprint, `sec-six-functors/sk-prop-sf-pf-coherence`,
`prop-sf-pf-coherence.proof.md`, compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison).

The finite clause retains the two etale-origin witnesses and uses the actual common-
refinement composite. The other clauses use the normalized completed, localized and
common-stage operations of the recorded six-functor datum. Only rho is an isomorphism.
-/

attribute [local irreducible] HasDerivedCategory.standard

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
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

/-- Projection transformations agree for any two compactifications, at every specified
coefficient stage, with no assertion of invertibility of a projection transformation.
The finite clause includes the actual input and target etale-origin witnesses. The
integral clause uses the uniform finite-reduction Tor predicate, and the two field
clauses range over their entire bounded constructible categories.
Source: main-20261015 blueprint, prop-sf-pf-coherence.proof.md,
compactification-independence sentence
(blueprint: lem-fix-projection-compactification-comparison).

Proof:
1. At finite coefficients, apply the two witnessed squares in finite_descent to the
   common refinement. Cancel the first comparison and compose with the second.
   The target-witness transports at the intermediate compactification cancel.
2. At higher coefficients, use integralRefinementProjection and its field transport
   fieldRefinementProjection. These are local equations for one proper refinement.
3. Choose a common refinement of the two compactifications. The comparison cocycle
   identifies its two-comparison composite with the prescribed comparison. Apply
   functoriality and the same cancellation calculation to obtain each higher law.
No projection transformation is inverted.
-/
theorem comparison
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k)) :
    finiteLaw D C E n hn hl ∧
    higherLaw S.higher.integral S.higher.integralTensor S.higher.integralExchange
      (fun Y K ↦ finiteTorConstructibleIntegral C.l E Y.obj.left K.obj) ∧
    higherLaw S.higher.rational S.higher.rationalTensor S.higher.rationalExchange
      (fun _ _ ↦ True) ∧
    higherLaw S.closure.commonStage S.closure.commonStageTensor S.closure.commonStageExchange
      (fun _ _ ↦ True) := by
  refine ⟨finiteCompactificationProjection D C E n hn S hl, ?_, ?_, ?_⟩
  · exact higherComparison _ _ _ _ (integralRefinementProjection D C E n hn S hl)
  · exact higherComparison _ _ _ _ (fieldRefinementProjection D C E n hn S hl).1
  · exact higherComparison _ _ _ _ (fieldRefinementProjection D C E n hn S hl).2

end WeilConjectures.FixProjectionCompactification
