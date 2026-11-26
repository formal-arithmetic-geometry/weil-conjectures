/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralCanonicalAmbientModels
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralComparisonRecursionLaws
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralExpressionCoefficientSquares
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel

/-! # Coherent integral realization of compactification expressions

We construct coherent integral realizations of compactification expressions and their maps.

## Implementation details

The comparisons are defined by induction on expression trees, using the actual unit and
counit of the reduction/limit adjunction on the complete and normalized domains. Generator
squares are proved before evaluation in the derived system category and then extended to all
expression contexts; no equality is inferred from finite evaluations.

## References

* [Stacks, Tag 0941]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus

private theorem good_counit_isIso (W : Scheme.{u}) (M : System l E W)
    (h : Good l E W M) : IsIso ((calculus l E W).adjunction.counit.app M) := by
  exact normalizedSequence_counit_isIso l E W (calculus l E W)
    M h.1

private theorem reduction_normalization
    {C N A : Type*} [Category C] [Category N] [Category A]
    {R : C ⥤ N} {L : N ⥤ C} (adj : R ⊣ L)
    (F : A ⥤ N) (G : A ⥤ C) (c : F ⋙ L ≅ G)
    (he : ∀ X : A, IsIso (adj.counit.app (F.obj X))) :
    ∃ r : F ≅ G ⋙ R, ∀ X : A,
      R.map (c.hom.app X) ≫ r.inv.app X = adj.counit.app (F.obj X) := by
  let e : (F ⋙ L) ⋙ R ≅ F :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (adj.counit.app (F.obj X)) (he X))
      (fun f ↦ adj.counit.naturality (F.map f))
  refine ⟨e.symm ≪≫ Functor.isoWhiskerRight c R, ?_⟩
  intro X
  change R.map (c.hom.app X) ≫ (R.map (c.inv.app X) ≫ _) = _
  rw [← Category.assoc, ← R.map_comp, c.hom_inv_id_app, R.map_id, Category.id_comp]
  rfl

private theorem coefficient_intertwining
    {C N : Type*} [Category C] [Category N]
    {R : C ⥤ N} {L : N ⥤ C} (adj : R ⊣ L)
    {M N₀ : N} {X Y : C} (c : L.obj M ≅ X) (d : L.obj N₀ ≅ Y)
    (s : M ⟶ N₀) (t : X ⟶ Y)
    (h : R.map c.inv ≫ adj.counit.app M ≫ s =
      R.map t ≫ R.map d.inv ≫ adj.counit.app N₀) :
    L.map s ≫ d.hom = c.hom ≫ t := by
  apply (cancel_epi c.inv).mp
  apply (cancel_mono d.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  apply (adj.homEquiv X N₀).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj.counit.naturality s
  change R.map (L.map s) ≫ adj.counit.app N₀ = adj.counit.app M ≫ s at hn
  rw [hn]
  exact h

/-- Coherent integral realization of compactification expressions and their maps. -/
theorem integralCompactificationSystemRealization
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) :
    ∃ o : Operations l E, Nonempty (Realizations l E D o) := by
  obtain ⟨o, ⟨a⟩⟩ := integralCanonicalAmbientModels l E
  obtain ⟨c, ⟨hc⟩⟩ := integralComparisonRecursionLaws l E D _hl o a
  have reductions {I : Type u} [Finite I]
      {X : I → Over (Spec (CommRingCat.of D.k))}
      {W : Over (Spec (CommRingCat.of D.k))}
      (e : Expression _ I X W) (g : e.geometric) :
      ∃ r : (e.domain l E o).ι ⋙ inputReduction l E X ⋙
          e.evaluate (systemInterpretation l E o) ≅
          e.realizationTarget l E o ⋙ (calculus l E W.left).reduction,
        ∀ K : (e.domain l E o).FullSubcategory,
          (calculus l E W.left).reduction.map ((c e g).hom.app K) ≫ r.inv.app K =
            (calculus l E W.left).adjunction.counit.app
              ((e.evaluate (systemInterpretation l E o)).obj
                ((inputReduction l E X).obj K.obj)) := by
    let F := (e.domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o)
    let G := e.realizationTarget l E o
    let ce : F ⋙ coefficientSequenceLimit l E W.left ≅ G :=
      NatIso.ofComponents (fun K ↦ (c e g).app K)
        (fun f ↦ (c e g).hom.naturality f)
    obtain ⟨r, hr⟩ := reduction_normalization (calculus l E W.left).adjunction F G ce
      (fun K ↦ good_counit_isIso l E W.left _
        (e.admissibleGood l E o _ K.property.2))
    exact ⟨r, hr⟩
  classical
  let r := fun {I : Type u} [Finite I]
      {X : I → Over (Spec (CommRingCat.of D.k))}
      {W : Over (Spec (CommRingCat.of D.k))}
      (e : Expression _ I X W) (g : e.geometric) ↦ (reductions e g).choose
  have hn := fun {I : Type u} [Finite I]
      {X : I → Over (Spec (CommRingCat.of D.k))}
      {W : Over (Spec (CommRingCat.of D.k))}
      (e : Expression _ I X W) (g : e.geometric) ↦ (reductions e g).choose_spec
  obtain ⟨hcomplete, hsquare, hsupport⟩ :=
    integralExpressionCoefficientSquares l E D _hl o a c hc r hn
  refine ⟨o, ⟨{
    compositors := a.compositors
    openComparisons := a.openComparisons
    canonicalBridge := a.canonicalBridge
    properOpen := a.properOpen
    ringedTensorCoherence := a.ringedTensorCoherence
    comparison := c
    realizationModel := a.realizationModel
    openRealization := a.openRealization
    openNormalization := a.openNormalization
    inputNormalization := hc.inputNormalization
    push := hc.push
    pull := hc.pull
    shriek := hc.shriek
    tensor := hc.tensor
    supportRecursion := hc.supportRecursion
    reduction := r
    normalization := hn
    ringedModels := a.ringedModels
    ringedOpenComparisons := a.ringedOpenComparisons
    ringedProperOpen := a.ringedProperOpen
    completionIso := hcomplete
    coherence := ?_
    compactSupport := hsupport }⟩⟩
  intro I _ X W e t ge gt K ht s v hpair
  exact coefficient_intertwining (calculus l E W.left).adjunction
    ((c e ge).app K) ((c t gt).app ⟨K.obj, ht⟩) s v
    (hsquare e t ge gt K ht s v hpair)

end IntegralSystemRealization
end WeilConjectures
