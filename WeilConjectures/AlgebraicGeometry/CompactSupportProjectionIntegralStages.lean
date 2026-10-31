/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleProjectionMates
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFiniteStages
import WeilConjectures.AlgebraicGeometry.IntegralStageProjectionReduction
import WeilConjectures.AlgebraicGeometry.IntegralStageProjectionStructuralIdentities
import WeilConjectures.AlgebraicGeometry.FixProjectionCompactificationComparison

/-! # Integral coefficient projection laws

The integral part of the compact-support projection formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

private theorem transported_bifunctor_component
    {A B : Type v} [Category.{w} A] [Category.{w} B]
    {F F' G' G : A ⥤ B ⥤ B} (e : F = F') (e' : G' = G)
    (τ : F' ⟶ G') (K : A) (L : B) :
    ((eqToHom e ≫ τ ≫ eqToHom e').app K).app L =
      eqToHom (congrArg (fun H : A ⥤ B ⥤ B ↦ (H.obj K).obj L) e) ≫
        (τ.app K).app L ≫
        eqToHom (congrArg (fun H : A ⥤ B ⥤ B ↦ (H.obj K).obj L) e') := by
  subst F'
  subst G
  simp

private theorem projection_naturality
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {K K' : B X} {L L' : B Y} (a : K ⟶ K') (b : L ⟶ L') :
    ((T Y).map ((S.support f c).map a)).app L ≫
        ((T Y).obj ((S.support f c).obj K')).map b ≫
        compactSupportProjectionComponent A f c K' L' =
      compactSupportProjectionComponent A f c K L ≫
        (S.support f c).map
          (((T X).map a).app ((S.pull f).obj L) ≫
            ((T X).obj K').map ((S.pull f).map b)) := by
  let Q := compactSupportProjectionSquare f c
  let d := A Q
  let V := (Functor.postcompose₂.obj (S.support f c)).obj
    ((((Functor.whiskeringLeft₂ (B X)).obj (𝟭 (B X))).obj (S.pull f)).obj (T X))
  let τ : S.support f c ⋙ T Y ⟶ V :=
    eqToHom (by rw [d.compactSupport, d.tensorY]; rfl) ≫ d.stage.projection ≫
      eqToHom (by rw [d.compactSupport, d.tensorX, d.pull]; rfl)
  have hτ (M : B X) (N : B Y) :
      (τ.app M).app N = compactSupportProjectionComponent A f c M N := by
    have h := transported_bifunctor_component
      (F := S.support f c ⋙ T Y) (G := V)
      (by rw [d.compactSupport, d.tensorY]; rfl)
      (by rw [d.compactSupport, d.tensorX, d.pull]; rfl)
      d.stage.projection M N
    dsimp only [τ, Q, d, V, compactSupportProjectionComponent,
      SixFunctorExchangeData.projectionComponent, compactSupportProjectionSquare,
      Functor.comp_obj, Functor.postcompose₂, Functor.whiskeringLeft₂] at h ⊢
    exact h
  have h₁ := congrArg (fun t ↦ t.app L) (τ.naturality a)
  have h₂ := (τ.app K').naturality b
  change ((T Y).map ((S.support f c).map a)).app L ≫ (τ.app K').app L =
    (τ.app K).app L ≫ (S.support f c).map (((T X).map a).app ((S.pull f).obj L)) at h₁
  change ((T Y).obj ((S.support f c).obj K')).map b ≫ (τ.app K').app L' =
    (τ.app K').app L ≫ (S.support f c).map
      (((T X).obj K').map ((S.pull f).map b)) at h₂
  simp only [← hτ]
  rw [h₂, ← Category.assoc, h₁, Category.assoc, ← Functor.map_comp]

private theorem integral_reductions_conservative
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D)
    {K L : sfIntegralConstructibleCategory C.l E X.obj.left} (a : K ⟶ L)
    (ha : ∀ m : ℕ, IsIso ((scalarReductionDerivedExtension C.l E X.obj.left m).map
      a.hom)) : IsIso a := by
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus C.l E X.obj.left
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (C.l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl₀ : C.l ≠ D₀.p := by change C.l ≠ p; omega
  have hK : IntegralOnSlice.IsComplete C.l E X.obj.left none K.obj :=
    ⟨D₀, hl₀,
      (sfDerivedComplete_iff_legacy C.l E X.obj.left D₀ hl₀ K.obj).mp K.property.1⟩
  have hL : IntegralOnSlice.IsComplete C.l E X.obj.left none L.obj :=
    ⟨D₀, hl₀,
      (sfDerivedComplete_iff_legacy C.l E X.obj.left D₀ hl₀ L.obj).mp L.property.1⟩
  have hred : IsIso (S.reduction.map a.hom) := by
    apply (S.isIso_iff_evaluations _).2
    intro m
    have hm : IsIso ((coefficientFiniteDerivedExtension C.l E X.obj.left m).map
        a.hom) := ha m
    exact (NatIso.isIso_map_iff (S.reductionEvaluation m) a.hom).mpr hm
  have huK := (purNormalizedReconstructionOfScheme C.l E X.obj.left S).2 K.obj hK
  have huL := (purNormalizedReconstructionOfScheme C.l E X.obj.left S).2 L.obj hL
  let _ := huK
  let _ := huL
  let _ := hred
  let _ : IsIso (a.hom ≫ S.adjunction.unit.app L.obj) := by
    have hnat := S.adjunction.unit.naturality a.hom
    simp only [Functor.id_map, Functor.comp_map] at hnat
    rw [hnat]
    change IsIso (S.adjunction.unit.app K.obj ≫
      (coefficientSequenceLimit C.l E X.obj.left).map (S.reduction.map a.hom))
    infer_instance
  let _ : IsIso a.hom := IsIso.of_isIso_comp_right a.hom (S.adjunction.unit.app L.obj)
  let _ : IsIso ((sfIntegralConstructible C.l E X.obj.left).ι.map a) := by
    simpa only [ObjectProperty.ι_map] using (inferInstance : IsIso a.hom)
  exact isIso_of_reflects_iso a (sfIntegralConstructible C.l E X.obj.left).ι

private theorem integral_stage_laws
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) :
    CompactSupportProjectionLaws S.higher.integral S.higher.integralTensor
      S.higher.integralExchange S.integralFiniteTorDomain := by
  obtain ⟨hcomp, hpent, hproper⟩ := integralStageProjection_structuralIdentities S
  refine ⟨?_, ?_, ?_, hcomp, hpent, hproper⟩
  · intro X Y f _ _ _ c K L hL
    apply integral_reductions_conservative Y
    intro m
    let R := sixFunctorIntegralReduction D C E m
    have hLm : finiteTorConstructible C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) Y.obj.left ((R Y).obj L).obj := by
      obtain ⟨a, b, _, htor⟩ := hL.2
      exact ⟨((R Y).obj L).property, a, b, htor m⟩
    let Lm : finiteTorConstructibleCategory C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) Y.obj.left := ⟨((R Y).obj L).obj, hLm⟩
    have hi := ((compactSupportProjectionFormula_finiteStages S).2.1 m).isIso
      f c ((R X).obj K) Lm
    let _ := hi
    have hfinite : IsIso (CompactSupportFiniteProjection.component
        (S.integralNormalization.finiteLevels m) f c ((R X).obj K) Lm).hom := by
      simpa only [ObjectProperty.ι_map] using
        (intrinsicFiniteTorsionConstructible C.l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) Y.obj.left).ι.map_isIso
          (CompactSupportFiniteProjection.component
            (S.integralNormalization.finiteLevels m) f c ((R X).obj K) Lm)
    obtain ⟨e⟩ := integralStageProjection_reduction S f c K L hL m Lm rfl
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).2 hfinite
  · intro X Y f _ _ _ c K K' L L' _ _ a b
    exact projection_naturality S.higher.integralExchange f c a b
  · intro X Y f _ _ _ c d K L hL
    have h := (FixProjectionCompactification.comparison D C E n hn S
      (PurCompactSupport.coefficientPrimeUnit C.l D C.different)).2.1 f c d K L hL
    exact h.symm

/-- The projection laws for the integral coefficient systems occurring in the datum.
Source: fix-prop-projection-formula.proof.md in
literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done;
reduction, adic reconstruction and coherence steps.
(blueprint: lem-sf-projection-integral-stage-laws).
Proof: the normalized reduction square identifies the finite reductions of the
specified integral projection map with the finite projection maps. The complete
constructible cone has zero first reduction by the finite-stage projection laws;
derived Nakayama therefore makes the integral map invertible on exactly the
uniform finite-Tor second-input domain. Naturality is the naturality of the
specified mate. Refinement, composition and the pentagon are identities of
coherent derived systems, obtained from the finite mate calculations with the
normalized transition maps. Realize those system identities and then take the
total limit, conjugating by the specified realization comparisons. This proves
map equalities before passing to limits, without detecting equality by finite
reduction. The identity-open compactification yields proper coincidence. The
same construction applies to every finite coefficient field in the closure. -/
theorem compactSupportProjectionFormula_integralStages
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) :
    CompactSupportProjectionLaws S.higher.integral S.higher.integralTensor
      S.higher.integralExchange S.integralFiniteTorDomain ∧
    ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      CompactSupportProjectionLaws (S.closure.coefficientStages E₀).integral
        (S.closure.coefficientStages E₀).integralTensor
        (S.closure.coefficientStages E₀).integralExchange
        (fun X K ↦ finiteTorConstructibleIntegral C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left K.obj) := by
  refine ⟨integral_stage_laws S, ?_⟩
  intro E₀
  let S₀ : SixFunctorOperationDatum D C
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀)
      (0 + 1) (Nat.succ_le_succ (Nat.zero_le 0)) :=
    { (S.coefficientIntegralNormalization E₀).finiteLevels 0 with
      higher := S.closure.coefficientStages E₀
      integralNormalization := S.coefficientIntegralNormalization E₀
      closure := S.closure
      coefficientIntegralNormalization := S.coefficientIntegralNormalization
      commonStageCoherence := S.commonStageCoherence }
  exact integral_stage_laws S₀

end WeilConjectures
