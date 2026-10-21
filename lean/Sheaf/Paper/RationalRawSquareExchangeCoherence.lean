/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.Paper.FiniteStageRationalExchangeData

/-! # Scalar compatibility of the composite rational exchange

Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-rational-raw-square-exchange-coherence)
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
compatible raw family.
Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-rational-raw-square-exchange-coherence).
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
compatible raw transformation. The composite normalization formulas follow by
cancelling the intervening integral/raw comparisons and their inverses. -/
theorem rationalRawSquareExchangeCoherence
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
  ∀ (E : Padic.FiniteCoefficientFields l Ω), HEq (rawAlpha.τ E)
    (sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq) := by sorry

end Square
end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
