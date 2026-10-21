/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.CompletedCoefficientPushforwardModels

/-! # Invertibility of the canonical strict reduction augmentation

Source: Stacks algebraization.tex Tag 0A0E; Bhatt--Scholze Definition 3.5.2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Completeness makes the specified chain-level reduction augmentation invertible
in any normalized total derived inverse-limit model.

Source: Stacks algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
Bhatt--Scholze Definition 3.5.2; Stacks sites-cohomology.tex, Tag 0941
(blueprint: lem-pur-completed-reduction-augmentation-iso).
Proof:
1. Use the chosen flat-term K-flat P to compute derived reduction at each positive
power of the uniformizer. The finite free two-term resolution of each quotient
identifies its derived tensor with the corresponding Koszul reduction. The maps of
these resolutions induce the given quotient transitions. The tensor units agree
on every section with x mapped to 1 tensor x.
2. Exact countable products of pro-etale module sheaves identify the explicit signed
Koszul fiber with the Roos model of this strict quotient tower. Its unit is the
zero-homotopy lift of the compatible tensor units. The Roos/intrinsic completeness
equivalence makes this particular unit invertible when K is complete. This uses the
normalized explicit unit, rather than an unspecified triangle isomorphism.
3. The strict Roos derivation computes total inverse limit. Its universal property
compares it with source.limit, preserving the comparison on every complex. The
augmentation a has precisely the tensor-unit formula, so under this comparison its
localized composite with source.limit.unit is the explicit unit from step 2.
Precomposing with r.inv gives the displayed map, and hence it is invertible.
Changing the exact or total derived models conjugates by isomorphisms and does not
change invertibility. No claim that a reduced inverse system is constant is used;
empty schemes give the identity map of a zero object. -/
theorem reductionAugmentation_isIso (p : ℕ) [Fact p.Prime] (hlp : l ≠ p)
    (W : Scheme.{t}) (source : SiteLimitData l E W)
    (K : DerivedCategory (Mod W (R l E W)))
    (P : CochainComplex (Mod W (R l E W)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hflat : ∀ i : ℤ, @SheafOfModules.IsFlatOnSite W.ProEt inferInstance (ProEt.topology W)
      inferInstance (integralCoefficientAbLocallyBijective.{t, u} W)
      (integralCoefficientAbSheafify.{t, u} W).isRightAdjoint
      (completedIntegralCommRingSheafUnrestricted l E W) (P.X i))
    (r : DerivedCategory.Q.obj P ≅ K)
    (C : CochainComplex (ℕᵒᵖ ⥤ Mod W (R l E W)) ℤ)
    (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E W P)
    (a : P ⟶ ((ordinaryTowerLimit l E W).mapHomologicalComplex (.up ℤ)).obj C)
    (ha : IsReductionAugmentation l E W P C e a)
    (hK : IsDerivedCompleteUnrestricted l E W K) :
    IsIso (r.inv ≫ DerivedCategory.Q.map a ≫ source.limit.unit.app C) := by
  sorry

end WeilConjectures.CompletedCoefficientPushforward
