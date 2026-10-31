/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCompletedTowerRoos
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerReconstruction
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.CompletedDerivedInverseLimit
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.SmoothPurityCompletedReductionAdjunction
import WeilConjectures.AlgebraicGeometry.SmoothPurityCompletedReductionConstructible

/-!
# Normalized coefficient towers and derived-complete integral complexes

Source: blueprint main-20261015, sec-smooth-purity,
`sk-lem-sp-tower/sk-lem-sp-tower-equivalence.md`; Bhatt--Scholze, Lemma 3.5.7
(blueprint: det-sp-normalized-equivalence).

## Main definitions and statements

- `spCompletedReduction`: the existing reduction transported to completed coefficients.
- `spCompletedTotalLimit`: exact scalar forgetting followed by total derived inverse limit.
- `spCompletedTotalProjection`: the resolution-normalized limit projections.
- `SpNormalizedEquivalence`: the adjunction, its isomorphisms, and constructible restriction.
- `sp_normalized_equivalence`: existence of this normalized equivalence data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The ambient reduction/total-limit adjunction, its isomorphisms on complete and
normalized objects, and its restriction to the recorded constructible categories.
Exact scalar forgetting is part of the construction, not an additional hypothesis.
Source: blueprint, normalized equivalence; Bhatt--Scholze, Lemma 3.5.7
(blueprint: det-sp-normalized-equivalence). -/
structure SpNormalizedEquivalence (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) where
  /-- Forgetting actions preserves componentwise addition. -/
  [forgetAdditive : (spCompletedStrictTower l E T D).Additive]
  /-- Forgetting actions preserves kernels and finite products. -/
  [forgetLimits : PreservesFiniteLimits (spCompletedStrictTower l E T D)]
  /-- Forgetting actions preserves cokernels and finite coproducts. -/
  [forgetColimits : PreservesFiniteColimits (spCompletedStrictTower l E T D)]
  /-- Total derived limit is exact, with its standard integer shift structure. -/
  [limitShift : (spCompletedTotalLimit l E T D).CommShift ℤ]
  /-- It carries distinguished triangles to distinguished triangles. -/
  limit_triangulated : (spCompletedTotalLimit l E T D).IsTriangulated
  /-- The products in the Roos triangle are products in the derived category. -/
  [products : HasCountableProducts
    (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))]
  /-- The Roos triangle uses the actual derived strict-tower transitions and the
  K-injective-normalized projections; it chooses no arbitrary lift from a triangle. -/
  roos : ∀ C : spDerivedCoefficientTowers l E T D,
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶
        ((spCompletedTotalLimit l E T D).obj C)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C)
        ((spCompletedTotalLimit l E T D).obj C)
        (Pi.lift (fun n : ℕ ↦ (spCompletedTotalProjection l E T D n).app C)) δ
  /-- The ambient adjunction on the ordinary unbounded derived categories. -/
  adjunction : spCompletedReduction l E T D R ⊣ spCompletedTotalLimit l E T D
  /-- No boundedness or constructibility is assumed on a derived-complete object. -/
  unit_isIso : ∀ M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T),
    WeilConjectures.IntegralOnSlice.IsComplete l E T none M →
      IsIso (adjunction.unit.app M)
  /-- No boundedness or constructibility is assumed on a normalized tower. -/
  counit_isIso : ∀ C : spDerivedCoefficientTowers l E T D,
    IsSpNormalizedTower l E T D C → IsIso (adjunction.counit.app C)
  /-- Only the constructible restriction assumes that T is Noetherian. The two
  equalities say that these are precisely the restrictions of reduction and total limit. -/
  restriction : IsNoetherian T →
    ∃ e : WeilConjectures.sfIntegralConstructibleCategory l E T ≌
        spNormalizedConstructibleTorTowerCategory l E T D,
      e.functor ⋙ (spNormalizedConstructibleTorTowers l E T D).ι =
        (WeilConjectures.sfIntegralConstructible l E T).ι ⋙ spCompletedReduction l E T D R ∧
      e.inverse ⋙ (WeilConjectures.sfIntegralConstructible l E T).ι =
        (spNormalizedConstructibleTorTowers l E T D).ι ⋙ spCompletedTotalLimit l E T D

private theorem integralConstructible_complete
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (hM : WeilConjectures.sfIntegralConstructible l E T M) :
    WeilConjectures.IntegralOnSlice.IsComplete l E T none M := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let F : WeilConjectures.FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ F.p := by change l ≠ p; omega
  exact ⟨F, hl, (WeilConjectures.sfDerivedComplete_iff_legacy l E T F hl M).mp hM.1⟩

/-- Reduction is left adjoint to total derived inverse limit, its unit is invertible
on derived-complete objects, and its counit on all normalized towers. On a Noetherian
scheme this restricts to the mutually inverse constructible equivalences.
Source: blueprint main-20261015, sk-lem-sp-tower-equivalence; Bhatt--Scholze,
Lemma 3.5.7(1)--(5) (blueprint: det-sp-normalized-equivalence).

Proof, following the ten DAG steps:
1. The DVR decomposition ell = unit times pi^e, e >= 1
(lem-weil-l-adic-extension-integers-dvr), identifies ell-power quotients with the
cofinal pi-power levels en. Use the actual strict system and the unbounded
uniformizer reduction/limit adjunction of lem-coef-derived-system-evaluation-calculus.
2. On fixed-ring towers, subsequence restriction has the exact ceiling-index left
adjoint, hence preserves K-injectives. Initiality of the subsequence gives the
projection-preserving total-limit isomorphism by lem-weil-pbc-initial-functor-limit
and lem-weil-pbc-ringed-strict-tower-homotopy-limit, with no product-exactness assumption.
3. On varying coefficients restriction has the exact floor-index right adjoint,
zero below e. Its Hom bijections descend to unbounded derived categories by
lem-sf-exact-functor-derived-triangulated; the selected composite is the identity.
4. Compose these Hom bijections with the uniformizer adjunction. Their naturality
gives the ambient adjunction. Its unit comes from strict quotient maps and its
counit is the tensor adjunct of the actual limit projections.
5. Use lem-pur-system-level-left-extension to interpolate any normalized ell-power
tower to the uniformizer levels. The ceiling formula, tensor associators, and
normalization make every transition-adjoint an isomorphism, including equal indices.
6. Apply lem-coef-normalized-dvr-effectivity to that tower. Its level comparisons are
the counit of step 4; derived evaluations detect isomorphisms. This proves the
counit clause without boundedness, Tor bounds or constructibility.
7. The reduction tower of every complex is normalized by K-flat change of rings
(lem-pur-kflat-change-of-rings). Effectivity and the triangular identity make the
unit at its completion invertible. For a derived-complete M, compare its augmented
Roos triangle with the total-limit triangle using TR3 and lem-sf-triangle-morphism-iso.
This gives M isomorphic to its completion. Naturality of the unit then makes its
actual component at M invertible; cofinality respects the quotient-map units.
8. Integral constructibility supplies constructible uniformizer reductions and a
common cohomological interval. Select the en levels and use lem-coef-integral-residue-tor
for a common Tor interval. The arbitrary-complex construction in
det-sp-reduction-tower-normalized supplies the strict normalized reduction tower.
Thus reduction lands in the recorded normalized constructible finite-Tor subcategory.
9. Conversely sk-lem-sp-tower puts the total limit of any such tower in the exact
sfIntegralConstructible category used here, with the same completed coefficients.
10. Restrict the two functors using steps 8 and 9. The unit and counit isomorphisms
of steps 7 and 6 retain naturality and the triangular identities on these full
subcategories and give mutually inverse equivalences. -/
theorem sp_normalized_equivalence
    [∀ x : T, Invertible (l : T.residueField x)]
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D) :
    Nonempty (SpNormalizedEquivalence l E T D R) := by
  let := D.hasDerived
  let products := WeilConjectures.integralOperationsDerivedCountableProducts l E T
  let := products
  obtain ⟨adj, hu, hc⟩ := spCompletedReduction_limitAdjunction l E T D R
  refine ⟨{ limit_triangulated := spCompletedTotalLimit_triangulated l E T D
            roos := spCompletedTotalLimit_roos l E T D
            adjunction := adj
            unit_isIso := hu
            counit_isIso := hc
            restriction := ?_ }⟩
  intro hT
  let := hT
  let P := WeilConjectures.sfIntegralConstructible l E T
  let Q := spNormalizedConstructibleTorTowers l E T D
  let F : P.FullSubcategory ⥤ Q.FullSubcategory := Q.lift
    (P.ι ⋙ spCompletedReduction l E T D R)
    (fun K ↦ spCompletedReduction_constructible l E T D R K.obj K.property)
  have hG (C : Q.FullSubcategory) :
      P ((spCompletedTotalLimit l E T D).obj C.obj) := by
    obtain ⟨δ, hδ⟩ := spCompletedTotalLimit_roos l E T D C.obj
    exact (spTower_reconstruction l E T D C.obj C.property.1 C.property.2
      ((spCompletedTotalLimit l E T D).obj C.obj)
      (Pi.lift (fun n : ℕ ↦ (spCompletedTotalProjection l E T D n).app C.obj)) δ hδ).1
  let G : Q.FullSubcategory ⥤ P.FullSubcategory := P.lift
    (Q.ι ⋙ spCompletedTotalLimit l E T D) hG
  let a : F ⊣ G := adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  have hunit (K : P.FullSubcategory) : (a.unit.app K).hom = adj.unit.app K.obj := by
    change P.ι.map (a.unit.app K) = _
    dsimp only [a]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    change adj.unit.app K.obj ≫ (spCompletedTotalLimit l E T D).map (𝟙 _) ≫ 𝟙 _ = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hcounit (C : Q.FullSubcategory) : (a.counit.app C).hom =
      adj.counit.app C.obj := by
    change Q.ι.map (a.counit.app C) = _
    dsimp only [a]
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    change 𝟙 _ ≫ (spCompletedReduction l E T D R).map (𝟙 _) ≫
      adj.counit.app C.obj = _
    simp only [CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp]
  have hunitIso (K : P.FullSubcategory) : IsIso (a.unit.app K) := by
    have := hu K.obj (integralConstructible_complete l E T K.obj K.property)
    have : IsIso (P.ι.map (a.unit.app K)) := by
      change IsIso ((a.unit.app K).hom)
      rw [hunit]
      infer_instance
    exact isIso_of_reflects_iso _ P.ι
  have hcounitIso (C : Q.FullSubcategory) : IsIso (a.counit.app C) := by
    have := hc C.obj C.property.2
    have : IsIso (Q.ι.map (a.counit.app C)) := by
      change IsIso ((a.counit.app C).hom)
      rw [hcounit]
      infer_instance
    exact isIso_of_reflects_iso _ Q.ι
  exact ⟨a.toEquivalence, rfl, rfl⟩

end AlgebraicGeometry.ProEtale
