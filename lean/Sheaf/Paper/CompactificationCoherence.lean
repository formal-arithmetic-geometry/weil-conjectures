/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.RefinementComparisonIsomorphism
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.ProperOpenComparison
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ClopenSectionDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.Paper.EtaleOriginDerivedCategory
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.ProEtaleProperOpenComparison
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory

/-!
# Compactification coherence on the witnessed etale-origin domain

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations,
prop-compactification-coherence, order 1485
(blueprint: prop-compactification-coherence-detailed).

The candidates and their specified objectwise comparisons are written in the canonical
fixed-scalar presentation of the recorded finite coefficient module categories. The
forgetful functor retains every ambient morphism between the witnessed objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The recorded compact-support candidate restricted to witnessed bounded below
etale-origin objects, in the fixed-scalar presentation used by the recorded refinement
comparison. The coefficient equivalence is the same one as `refinementFixedObject`;
objects, maps, and witnesses are transported canonically, without a new choice of map.
Source: blueprint prop-compactification-coherence, displayed candidates and final scope
paragraph, order 1485 (blueprint: prop-compactification-coherence-detailed). -/
def compactificationOriginCandidate (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    RefinementFiniteLevelOrigin l E n hn X ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
    discreteTopology_bot _
  etaleOriginForgetful X (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) ⋙
    (refinementCoefficientEquivalence X
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))).inverse ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) c

/-- The canonical refinement maps form natural isomorphisms, are unital and transitive,
and determine comparison isomorphisms independently of the common refinement and its
arrows. Every finite family has a common refinement, including the empty family; the
pairwise comparisons satisfy the cocycle law. The normalization by the recorded
`refinementComparisonIsomorphism` specifies the proper-composition map followed by
proper pushforward of the inverse proper-open map, rather than an arbitrary isomorphism.
The domain consists of bounded below etale-origin triples, with all ambient morphisms.

Source: blueprint prop-compactification-coherence, statement and proof paragraphs 1--4,
order 1485 (blueprint: prop-compactification-coherence-detailed).

Proof plan:
1. Finite type over the field makes X, Y and every proper compactification Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Refinements are proper, hence qcqs
   (def-weil-compactifications-refinements and lem-weil-pbc-proper-fp-permanence).
2. In the defining etale proper-open map, derived open restriction, extension-zero
   base change, and restriction to the clopen section are natural. Compose their
   naturality squares and invert the restriction comparison; the adjunction counit
   gives naturality of the specified etale proper-open map
   (def-weil-pbc-proper-open-comparison, lem-weil-pbc-derived-open-restriction,
   cor-cbc-derived-extension-zero-base-change, lem-weil-pbc-clopen-section-direct-image).
3. Transport this square using the natural extension-zero site comparison and the
   direct-image comparison; exactness descends the termwise construction to complexes
   and roofs (lem-cbc-proetale-extension-zero-comparison,
   lem-weil-pbc-extension-by-zero-exact, def-sf-comparison-derived-pullback,
   prop-weil-pbc-comparison-direct-image, lem-weil-pbc-proper-open-comparison-proetale).
4. Conjugate by the retained alpha. Full faithfulness of comparison pullback lifts
   every ambient map between witnessed objects to an etale map, proving naturality
   for all domain morphisms. The identity map between two witnesses gives witness
   independence (def-sf-etale-origin-subcategory, thm-weil-pbc-site-comparison).
5. Invert that proper-open isomorphism and apply the proper direct image after its
   canonical compositor. This is precisely refinementComparisonIsomorphism; naturality
   of its two factors gives theta (def-sf-refinement-comparison-isomorphism,
   lem-weil-derived-direct-image-composition, def-weil-compact-support-candidate).
6. The proper-open identity and composition laws survive witness conjugation: cancel
   the intermediate witness maps and move the compositor past alpha by naturality.
   Associativity of the direct-image compositor then gives theta_id and theta_comp
   (lem-weil-pbc-proper-open-comparison-proetale,
   lem-weil-derived-direct-image-composition).
7. For d mapping to c1 and c2, put T12 = theta(d,c1)^(-1) followed by theta(d,c2).
   Transitivity cancels theta for any further refinement of d.
8. For two choices d,d', first take a common refinement and successively equalize
   the two resulting parallel arrows to c1 and to c2. The first equality survives
   the second precomposition. Step 7 identifies the resulting comparisons, including
   different choices of arrows (prop-compactification-refinement).
9. Use the finite-family clause of the same cofilteredness theorem. A single common
   refinement for three objects cancels the middle theta and proves the cocycle law.
   Nonemptiness handles the empty family and identities handle a singleton. All these
   equations are on the witnessed domain, never on arbitrary pro-etale complexes. -/
theorem compactification_coherence (K₀ : Type u) [Field K₀]
    (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : K₀))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ theta : ∀ (c₁ c₂ : Compactification f) (_r : c₁ ⟶ c₂),
        compactificationOriginCandidate l E n hn c₁ ≅
          compactificationOriginCandidate l E n hn c₂,
      (∀ (c₁ c₂ : Compactification f) (r : c₁ ⟶ c₂)
          (O : RefinementFiniteLevelOrigin l E n hn X),
        (theta c₁ c₂ r).app O =
          refinementComparisonIsomorphism K₀ l hl E n hn f r O) ∧
      (∀ c : Compactification f, theta c c (𝟙 c) = Iso.refl _) ∧
      (∀ (c₁ c₂ c₃ : Compactification f) (r : c₁ ⟶ c₂) (s : c₂ ⟶ c₃),
        theta c₁ c₃ (r ≫ s) = theta c₁ c₂ r ≪≫ theta c₂ c₃ s) ∧
      (∀ (m : ℕ) (c : Fin m → Compactification f),
        ∃ d : Compactification f, ∀ i : Fin m, Nonempty (d ⟶ c i)) ∧
      ∃ comparison : ∀ c₁ c₂ : Compactification f,
          compactificationOriginCandidate l E n hn c₁ ≅
            compactificationOriginCandidate l E n hn c₂,
        (∀ (c₁ c₂ d : Compactification f) (r₁ : d ⟶ c₁) (r₂ : d ⟶ c₂),
          comparison c₁ c₂ = (theta d c₁ r₁).symm ≪≫ theta d c₂ r₂) ∧
        (∀ c₁ c₂ c₃ : Compactification f,
          comparison c₁ c₂ ≪≫ comparison c₂ c₃ = comparison c₁ c₃) := by
  sorry

end AlgebraicGeometry.ProEtale
