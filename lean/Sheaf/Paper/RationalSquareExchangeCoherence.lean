/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.Paper.FiniteStageRationalExchangeData
import Sheaf.Paper.RationalRawSquareExchangeCoherence
import Sheaf.Paper.FiniteStageKaroubiExtension

/-! # Scalar compatibility of the composite rational exchange

Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-rational-square-exchange-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Idempotents AlgebraicGeometry WeilConjectures
open AlgebraicGeometry.Scheme
universe w

attribute [local irreducible] pbcAmbientCompleteRawSystem

namespace AlgebraicGeometry.Scheme.FiniteStageRationalExchange
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section Square

variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x))]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
  [iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
  (sq : ChosenCartesianSquare h e f g)

/-- Given the canonical operation comparisons on the four sides, their composites
have the specified localized normalizations and carry the canonical exchange to a
compatible family before and after Karoubi extension.
Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-rational-square-exchange-coherence).
Proof: compose the push/pull morphisms of scalar systems. Their comparison components
are the outer comparison evaluated on the inner operation, followed by the outer
operation applied to the inner comparison. Naturality moves the middle factors,
so the two individual tower equations imply the composite tower equations. At an
identity transition the two identity comparisons compose to the identity.
On integral objects the two normalization formulas cancel the intervening inverse
integral/raw comparisons, giving the displayed composite normalization formulas.
Identify the integral completed mate with the ambient mate followed by completion:
precomposition by the pullback completion unit gives the ambient mate followed by
the direct image of the target unit. The reflected compositor unit-normalization
and reflector-square mate-factorization prove this equality uniquely. Apply the
published scalar-exchange equation to this mate, and then localize the equality.
Every raw object is integral, so the resulting components define the required
compatible raw transformation. Apply functorExtension₂ to the systems, comparisons
and transformation. Whiskering with the identity-projector inclusion is fully
faithful, so its raw checks prove the tower and exchange equations on every projector.
The supported component formulas preserve units and give precisely the stated maps. -/
theorem rationalSquareExchangeCoherence
    (cf_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) f ⋙
        pbcAmbientCompleteIntegralTransition l Ω S a ≅
      pbcAmbientCompleteIntegralTransition l Ω X a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) f)
    (cf_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) f ⋙
        pbcAmbientCompleteIntegralTransition l Ω X a ≅
      pbcAmbientCompleteIntegralTransition l Ω S a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) f)
    (cf_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω X)
    (pbcAmbientCompleteRawSystem l Ω S))
    (cf_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω S)
    (pbcAmbientCompleteRawSystem l Ω X))
    (cg_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) g ⋙
        pbcAmbientCompleteIntegralTransition l Ω S a ≅
      pbcAmbientCompleteIntegralTransition l Ω T a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) g)
    (cg_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) g ⋙
        pbcAmbientCompleteIntegralTransition l Ω T a ≅
      pbcAmbientCompleteIntegralTransition l Ω S a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) g)
    (cg_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω S))
    (cg_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω S)
    (pbcAmbientCompleteRawSystem l Ω T))
    (ch_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) h ⋙
        pbcAmbientCompleteIntegralTransition l Ω X a ≅
      pbcAmbientCompleteIntegralTransition l Ω Y a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) h)
    (ch_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) h ⋙
        pbcAmbientCompleteIntegralTransition l Ω Y a ≅
      pbcAmbientCompleteIntegralTransition l Ω X a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) h)
    (ch_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω Y)
    (pbcAmbientCompleteRawSystem l Ω X))
    (ch_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω X)
    (pbcAmbientCompleteRawSystem l Ω Y))
    (ce_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) e ⋙
        pbcAmbientCompleteIntegralTransition l Ω T a ≅
      pbcAmbientCompleteIntegralTransition l Ω Y a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) e)
    (ce_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) e ⋙
        pbcAmbientCompleteIntegralTransition l Ω Y a ≅
      pbcAmbientCompleteIntegralTransition l Ω T a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) e)
    (ce_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω Y)
    (pbcAmbientCompleteRawSystem l Ω T))
    (ce_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω Y))
    (hf : HasOperationCoherence l Ω f cf_pPush cf_pPull cf_rPush cf_rPull)
    (hg : HasOperationCoherence l Ω g cg_pPush cg_pPull cg_rPush cg_rPull)
    (hh : HasOperationCoherence l Ω h ch_pPush ch_pPull ch_rPush ch_rPull)
    (he : HasOperationCoherence l Ω e ce_pPush ce_pPull ce_rPush ce_rPull) :
  ∃ (rawF : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω X)),
  ∃ (rawG : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω X)),
  ∃ (_rawF_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    rawF.Φ E = sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g)),
  ∃ (_rawG_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    rawG.Φ E = sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h)),
  ∃ (_rawF_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (rawF.Φ E).Additive),
  ∃ (_rawG_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (rawG.Φ E).Additive),
  ∃ (_rawF_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (rawF.β (le_refl E)) (Iso.refl (rawF.Φ E))),
  ∃ (_rawG_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (rawG.β (le_refl E)) (Iso.refl (rawG.Φ E))),
  ∃ (_rawF_composite : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : pbcAmbientCompleteStage l Ω T E),
    HEq ((rawF.β a).hom.app K)
      ((cf_rPull.β a).hom.app ((cg_rPush.Φ E).obj K) ≫
        (cf_rPull.Φ M).map ((cg_rPush.β a).hom.app K))),
  ∃ (_rawG_composite : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : pbcAmbientCompleteStage l Ω T E),
    HEq ((rawG.β a).hom.app K)
      ((ch_rPush.β a).hom.app ((ce_rPull.Φ E).obj K) ≫
        (ch_rPush.Φ M).map ((ce_rPull.β a).hom.app K))),
  ∃ (_rawF_normalization : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    HEq ((rawF.β a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf_pPull a).hom.app
              ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map
              ((cg_pPush a).hom.app K)) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M)
          (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).inv.app K))),
  ∃ (_rawG_normalization : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    HEq ((rawG.β a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch_pPush a).hom.app
              ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map
              ((ce_pPull a).hom.app K)) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M)
          (h := h) (e := e)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).inv.app K))),
  ∃ (rawAlpha : StageSystem.Morphism.Hom rawF rawG),
  ∃ (_rawAlpha_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω), HEq (rawAlpha.τ E)
    (sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq)),
  ∃ (karF : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T)
    (pbcAmbientCompleteSystem l Ω X)),
  ∃ (karG : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T)
    (pbcAmbientCompleteSystem l Ω X)),
  ∃ (_karF_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    karF.Φ E = (functorExtension₂ _ _).obj (rawF.Φ E)),
  ∃ (_karG_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    karG.Φ E = (functorExtension₂ _ _).obj (rawG.Φ E)),
  ∃ (_karF_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (karF.Φ E).Additive),
  ∃ (_karG_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (karG.Φ E).Additive),
  ∃ (_karF_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (karF.β a) ((functorExtension₂ _ _).mapIso (rawF.β a))),
  ∃ (_karG_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (karG.β a) ((functorExtension₂ _ _).mapIso (rawG.β a))),
  ∃ (_karF_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (karF.β (le_refl E)) (Iso.refl (karF.Φ E))),
  ∃ (_karG_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (karG.β (le_refl E)) (Iso.refl (karG.Φ E))),
  ∃ (karAlpha : StageSystem.Morphism.Hom karF karG),
  ∀ (E : Padic.FiniteCoefficientFields l Ω), HEq (karAlpha.τ E)
    ((functorExtension₂ _ _).map (sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq)) := by
  obtain ⟨rawF, rawG, hF, hG, aF, aG, uF, uG, cF, cG, nF, nG, α, hα⟩ :=
    rationalRawSquareExchangeCoherence l Ω sq @cf_pPush @cf_pPull cf_rPush cf_rPull
      @cg_pPush @cg_pPull cg_rPush cg_rPull @ch_pPush @ch_pPull ch_rPush ch_rPull
      @ce_pPush @ce_pPull ce_rPush ce_rPull hf hg hh he
  have hExt := completeKarHom_exists l Ω (U := T) (V := X) (F := rawF) (G := rawG) α uF uG
  obtain ⟨kF, kG, η, hsF, hsG, hη⟩ := hExt
  obtain ⟨hkF, hbKF, huKF⟩ := hsF
  obtain ⟨hkG, hbKG, huKG⟩ := hsG
  refine ⟨rawF, rawG, hF, hG, aF, aG, uF, uG, @cF, @cG, @nF, @nG, α, hα,
    kF, kG, hkF, hkG,
    ?_, ?_, @hbKF, @hbKG,
    huKF, huKG,
    η, ?_⟩
  · intro E
    rw [hkF E]
    let := aF E
    infer_instance
  · intro E
    rw [hkG E]
    let := aG E
    infer_instance
  · intro E
    have h := hη E
    have hτ := extension_map_heq (hF E) (hG E) (α.τ E)
      (sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq) (hα E)
    exact h.trans hτ

end Square
end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
