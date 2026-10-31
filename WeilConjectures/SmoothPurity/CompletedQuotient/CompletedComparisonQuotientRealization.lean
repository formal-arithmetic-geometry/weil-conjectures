/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientNormalization
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonCanonicalIdentification
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonScalarLimitImage

/-! # Simultaneous quotient realization of completed comparisons

The normalization, canonical identification and scalar realization steps are
combined with the whole-system counit and structural transport calculations.
(blueprint: lem-pur-completed-comparison-quotient-realization).
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substituteInputs substitution strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Simultaneous quotient realization of completed comparison diagrams.

Source: integral finite-reduction and inverse-limit compatibility in
`def-weil-derived-pullback-tensor-hom`; Stacks 07A4, 07A2, 06YS, 0G7E, 0941;
Bhatt--Scholze Definition 3.4.10 and Lemma 6.5.9(4)
(blueprint: lem-pur-completed-comparison-quotient-realization).

Proof:
1. Apply quotient-expression K-flat normalization to the three arbitrary flat-term
   K-flat representatives. Ordinary reduction gives their actual quotient towers;
   its evaluation comparison and adjunction fix every quotient transition. Closure
   under units, total tensor and inverse image proves good and normalization for
   every finite expression, including unbounded complexes and repeated inputs.
   Actual derived-complete reconstruction makes the leaf units invertible.
   Primitive tensor and pullback counit comparisons give exactly substitution by
   induction on the expression, and show that it and its coherent reduction are
   isomorphisms. Naturality follows from their defining functor comparisons.
2. Cochain pullback--tensor coherence supplies comparison and its inverse with the
   insertion-of-one and multiplication formulas. These are maps on the sequence
   site, hence retain all transitions. Apply total derived limit to the inverse
   equations. The primitive counit normalization identifies their conjugates by
   substitution with the already fixed canonicalIntegralPullbackTensor maps.
3. On representatives all maps are natural by the tensor generator formulas.
   K-flat localization and its product universal property descend this naturality
   to all derived morphisms. The canonical comparison is therefore independent
   of simultaneous representatives. The displayed naturality equation for
   substitutions follows before localization and then under total limit.
4. Write e for the actual coherent counit. For every strict v:A to B, naturality
   gives R(L(v)) >> e_B = e_A >> Q(v). Insert beta_A, beta_B and cancel the latter
   with its inverse to obtain R(transport(v)) >> r_B = r_A >> Q(v). This equation
   is in the category of whole derived systems. The first square determines the
   completed structural iso uniquely, and this equation gives its finite reductions.
5. The generator-normalized strong monoidal comparisons satisfy associativity,
   both action-unit equations, Koszul-signed symmetry and the adjunction-normalized
   pullback composition equation. Apply total limit to these strict diagrams and
   insert the substitution maps. Adjacent inverse substitutions cancel, producing
   the specified completed structural diagrams and the same counit reductions.
6. K-flat coefficient change and the coefficient-extension reduction model give
   the normalized scalar quotient models. Balanced association sends
   (x tensor a) tensor b to x tensor iota(a)*b; its inverse inserts one. It
   commutes with every quotient transition. The normalized scalar, tensor and
   pullback realization equations identify these strict maps with the canonical
   completed scalar comparisons. This works for ramified extensions because it
   uses flat-term K-flat representatives, never flatness of the finite ring map.
7. The two strict scalar square routes both send b tensor (x tensor y) to
   (b tensor x) tensor (1 tensor y). Balancing and local tensor generation prove
   equality, also for inverses. Identity coefficients give the action unitors;
   successive extensions multiply the two coefficients and give the stated
   associator equations. Total limit, normalized scalar realization and step 2
   identify each route with the same limit conjugate in ScalarLimitImage, using
   scalarSubstitution of the E source and the recursive scalarBeta at the L target.
   scalarTransport at L is gamma_L by the canonical representative normalization;
   the other route uses this item's E transport. Thus both gamma/alpha composites
   equal the total-limit image of each actual strict route.
   Functoriality preserves the inverse, identity and successive-extension laws.
-/
theorem completedComparisonQuotientRealization
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj) :
    ∃ (good : GoodExpressions l E h f P)
      (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
        IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A)),
    (∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      (∀ n : ℕ, StrictQuotient.Good l E
        (strictValue l E (fun i ↦ quotient l E (P i).obj) A) n) ∧
      IsNormalizedCoefficientSequence l E W
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) ∧
      IsIso (reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good A))) ∧
    (∀ i : Fin 3, CoefficientReductionPresentation l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction
      (P i).obj (P i).property.1 (quotient l E (P i).obj)
      ((pullbackTensorReductionModel l E Y).app (P i))
      (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app (P i).obj).symm)) ∧
    (transport l E P (fun i ↦ (M i).obj) φ good invertible
      (sourceExpression h f) (targetExpression h f)
      (comparison l E f (quotient l E (P 0).obj) (quotient l E (P 1).obj)).hom =
        (canonicalIntegralPullbackTensor l E f (M 0) (M 1)).hom.hom) ∧
    (transport l E P (fun i ↦ (M i).obj) φ good invertible
      (targetExpression h f) (sourceExpression h f)
      (comparison l E f (quotient l E (P 0).obj) (quotient l E (P 1).obj)).inv =
        (canonicalIntegralPullbackTensor l E f (M 0) (M 1)).inv.hom) ∧
    (∀ {W : Scheme.{u}} (A B : StrictQuotient.Expression h f 3 W)
      (v : strictValue l E (fun i ↦ quotient l E (P i).obj) A ⟶
        strictValue l E (fun i ↦ quotient l E (P i).obj) B),
      (pullbackTensorCalculus l E W).reduction.map
          (transport l E P (fun i ↦ (M i).obj) φ good invertible A B v) ≫
        reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good B) =
      reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good A) ≫
        DerivedCategory.Q.map v) ∧
    (∀ {W : Scheme.{u}} (A B : StrictQuotient.Expression h f 3 W)
      (α : CompletedOperations.StructuralMap (expression A) (expression B)),
      ∃! c : (value l E A).obj (fun i ↦ (M i).obj) ≅
        (value l E B).obj (fun i ↦ (M i).obj),
      c.hom ≫ substitution l E P (fun i ↦ (M i).obj) φ good B =
        substitution l E P (fun i ↦ (M i).obj) φ good A ≫
          (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map
            (IntegralCoherence.structuralValue l E
              (fun i ↦ quotient l E (P i).obj) α).hom) ∧
      (pullbackTensorCalculus l E W).reduction.map c.hom ≫
        reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good B) =
      reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good A) ≫
        DerivedCategory.Q.map (IntegralCoherence.structuralValue l E
          (fun i ↦ quotient l E (P i).obj) α).hom) ∧
    NaturalSubstitution l E M P φ good ∧
    StrictCoherence l E h f ∧ StrictCoherence l L h f ∧
    NaturalComparison l E f ∧ NaturalComparison l L f ∧
    (∀ (d : Bool) (W : Scheme.{u}) (A : ScalarComplex l E L d W),
      ScalarGenerated l E L ι h f (fun i ↦ quotient l E (P i).obj) d W A →
        ScalarGood l E L d W A) ∧
    ScalarLimitImage l E L ι h f M P φ good invertible ∧
    ScalarIdentity l E f ∧ ScalarIdentity l L f ∧
    (∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
      (j : L →ₐ[ℚ_[l]] F), ScalarComposition l E L ι F j f) ∧
    (∀ (hlX : IsUnit (l : Γ(X, ⊤))) (hlY : IsUnit (l : Γ(Y, ⊤)))
      (SE : CoefficientDerivedSystemCalculus l E Y)
      (SL : CoefficientDerivedSystemCalculus l L Y)
      (A : CoefficientExtensionSystems l E L ι Y)
      (A0 : CoefficientExtensionSystems l E E (AlgHom.id ℚ_[l] E) Y),
      ScalarAssociation l E L ι f hlX hlY SE SL A A0 (M 0) (M 1)
        (P 0) (P 1) (φ 0) (φ 1)) := by
  obtain ⟨good, invertible, hnorm, hpresentation, hnatural⟩ :=
    completedComparisonQuotientNormalization l E h f M P φ
  obtain ⟨hcomparison, hcohE, hcohL, hnatE, hnatL⟩ :=
    completedComparisonCanonicalIdentification l E L h f M P φ good invertible
  obtain ⟨hscalarGood, hscalarLimit⟩ :=
    completedComparisonScalarLimitImage l E L ι h f M P φ good invertible
  have transportSquare {W : Scheme.{u}} (A B : StrictQuotient.Expression h f 3 W)
      (v : strictValue l E (fun i ↦ quotient l E (P i).obj) A ⟶
        strictValue l E (fun i ↦ quotient l E (P i).obj) B) :
      transport l E P (fun i ↦ (M i).obj) φ good invertible A B v ≫
          substitution l E P (fun i ↦ (M i).obj) φ good B =
        substitution l E P (fun i ↦ (M i).obj) φ good A ≫
          (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map v) := by
    have := invertible B
    unfold transport
    simpa only [Category.assoc, Category.comp_id, asIso_hom] using
      congrArg (fun k ↦ substitution l E P (fun i ↦ (M i).obj) φ good A ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map v) ≫ k)
        (asIso (substitution l E P (fun i ↦ (M i).obj) φ good B)).inv_hom_id
  have transportReduction {W : Scheme.{u}} (A B : StrictQuotient.Expression h f 3 W)
      (v : strictValue l E (fun i ↦ quotient l E (P i).obj) A ⟶
        strictValue l E (fun i ↦ quotient l E (P i).obj) B) :
      (pullbackTensorCalculus l E W).reduction.map
          (transport l E P (fun i ↦ (M i).obj) φ good invertible A B v) ≫
        reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good B) =
      reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good A) ≫
        DerivedCategory.Q.map v := by
    simp only [reduction]
    rw [← Functor.map_comp_assoc, transportSquare, Functor.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
      congrArg ((pullbackTensorCalculus l E W).reduction.map
        (substitution l E P (fun i ↦ (M i).obj) φ good A) ≫ ·)
        ((pullbackTensorCalculus l E W).adjunction.counit.naturality
          (DerivedCategory.Q.map v))
  refine ⟨good, invertible, hnorm, hpresentation, hcomparison, ?_, ?_, ?_,
    hnatural, hcohE, hcohL, hnatE, hnatL, hscalarGood, hscalarLimit, ?_, ?_, ?_, ?_⟩
  · have := invertible (sourceExpression h f)
    have := invertible (targetExpression h f)
    let c := asIso (substitution l E P (fun i ↦ (M i).obj) φ good
        (sourceExpression h f)) ≪≫
      (coefficientSequenceLimit l E X).mapIso
        (DerivedCategory.Q.mapIso
          (comparison l E f (quotient l E (P 0).obj) (quotient l E (P 1).obj))) ≪≫
      (asIso (substitution l E P (fun i ↦ (M i).obj) φ good
        (targetExpression h f))).symm
    let d := (canonicalIntegralPullbackTensor l E f (M 0) (M 1))
    unfold transport at hcomparison
    have hc : c.hom = d.hom.hom := by
      dsimp only [c, d]
      erw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
        Iso.symm_hom, asIso_hom]
      exact hcomparison
    have hi : c.inv = d.inv.hom := by
      apply (cancel_mono c.hom).1
      rw [c.inv_hom_id, hc]
      exact (ObjectProperty.isoInv_hom_id_hom d).symm
    dsimp only [c, d] at hi
    erw [Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Functor.mapIso_inv, asIso_hom, Category.assoc] at hi
    exact hi
  · exact transportReduction
  · intro W A B α
    have := invertible A
    have := invertible B
    let v := IntegralCoherence.structuralValue l E
      (fun i ↦ quotient l E (P i).obj) α
    let c := asIso (substitution l E P (fun i ↦ (M i).obj) φ good A) ≪≫
      (coefficientSequenceLimit l E W).mapIso (DerivedCategory.Q.mapIso v) ≪≫
      (asIso (substitution l E P (fun i ↦ (M i).obj) φ good B)).symm
    refine ⟨c, ⟨?_, ?_⟩, ?_⟩
    · simpa only [c, v, transport, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom, asIso_hom] using transportSquare A B v.hom
    · simpa only [c, v, transport, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom, asIso_hom] using transportReduction A B v.hom
    · intro d hd
      apply Iso.ext
      apply (cancel_mono (substitution l E P (fun i ↦ (M i).obj) φ good B)).1
      rw [hd.1]
      simpa only [c, v, transport, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom, asIso_hom] using (transportSquare A B v.hom).symm
  · unfold ScalarIdentity
    exact ScalarExtensionTower.unit l E f
  · unfold ScalarIdentity
    exact ScalarExtensionTower.unit l L f
  · intro F _ _ _ j
    unfold ScalarComposition
    exact ScalarExtensionTower.composition l E L ι F j f
  · intro hlX hlY SE SL A A0
    unfold ScalarAssociation
    exact ScalarExtensionTower.quotientModels l E L ι f hlX hlY SE SL A A0
      (M 0) (M 1) (P 0) (P 1) (φ 0) (φ 1)

end WeilConjectures.CompletedQuotient
