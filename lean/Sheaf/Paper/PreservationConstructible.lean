/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedTowerDirectImage
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.FiniteLevelAmplification
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.Paper.RestrictionDirectImage
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.AmplificationProper
import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity
import Sheaf.Paper.NormalizedEtaleOriginWitnesses
import Sheaf.Paper.PerfectProjectionFormula

/-! # Constructible preservation over completed integral coefficients

Source: Weil blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1355
(blueprint: prop-weil-pbc-preservation-constructible).
The four outputs use the actual completed coefficient ring, ordinary uncompleted
right derived direct image, and the strict-tower completed pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- A common cohomological support bound for every positive canonical reduction.
This only asserts vanishing outside the closed interval, with no Tor-amplitude claim.
The original small-site quotient module retains its coefficient action.
Source: blueprint order 1355, final paragraph
(blueprint: prop-weil-pbc-preservation-constructible). -/
def pbcReductionsCohomologyIn (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (a b : ℤ) (K : PbcCompletedDerived T d) : Prop :=
  ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
    IsZero ((DerivedCategory.homologyFunctor
      (pbcModules T ((pbcAdicRings T d).obj (op n))) q).obj
        ((pbcCompletedReduction T d n).obj K))

/-- Simultaneous preservation and reduction support bounds for the four outputs.
Source: blueprint order 1355; Stacks 09C1, 09C7, 095U, 0GL0 and 09C2
(blueprint: prop-weil-pbc-preservation-constructible).

Proof plan, following the node's five steps:
1. Residue characteristic l divides N; invertibility of N therefore makes l invertible.
Apply thm-weil-pbc-amplification-proper with the geometric fibre bound e to get AMP(2e).
The common local models of the input tower imply intrinsic constructible cohomology;
lem-weil-pbc-finite-ring-constructible-derived-origin identifies its finite etale origins.
2. For any complete output with canonical reductions constructible in one interval,
lem-weil-pbc-normalized-constructible-local-effectivity gives common local models,
compatible with the canonical normalization maps. Choose etale origins levelwise by
lem-weil-pbc-finite-ring-constructible-derived-origin. The canonical inverse-image/tensor
comparison is computed on K-flat flat-term resolutions by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and the exact comparison of
prop-weil-pbc-site-comparison-finite-level. Full faithfulness from
thm-weil-pbc-site-comparison uniquely lifts each normalization and its inverse.
Faithfulness lifts its identity and quotient cocycle. These witnesses give membership
by def-weil-pbc-bounded-constructible-complete.
3. For H = Rf_*K, prop-weil-pbc-direct-image-limits gives completeness. The completed-
coefficient projection isomorphism of lemma-weil-pbc-perfect-projection-formula induces
quotient-linear cohomology isomorphisms: locally lift quotient scalars to A_Y, apply
A_Y-linearity, and use annihilation by I^n for independence. FIN and
prop-weil-pbc-restriction-direct-image give constructibility and [a,b+2e] for these
canonical reductions. Apply step 2; no derived quotient-linear lift is assumed.
4. lemma-weil-pbc-completed-pullback-reduction gives completeness and quotient-linear
reduction comparisons for completed pullbacks of K and H. The interval-preserving
pullback clauses of def-weil-pbc-finite-level-amplification give [a,b] and [a,b+2e].
Apply the finite derived-origin criterion and step 2 to both canonical towers.
5. For Rf'_* of the pulled-back K, repeat step 3: completeness follows from direct-image
limits; the projection comparison is quotient-linear on cohomology by locally lifting
scalars, using lem-weil-pbc-constant-completion-equivalence. FIN for f' puts the
reductions in [a,b+2e]. Step 2 gives the fourth category membership. These are support
containments, including zero objects and empty schemes, rather than equalities. -/
theorem pbc_preservation_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (_square : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (_hDimX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (_hDimY : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (_hDimX' : ∃ d : ℕ, topologicalKrullDim X' ≤ (d : WithBot ℕ∞))
    (_hDimY' : ∃ d : ℕ, topologicalKrullDim Y' ≤ (d : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (_hN : 0 < N)
    (_hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0)
    (_hInvertX : IsUnit (N : Γ(X, ⊤))) (_hInvertY : IsUnit (N : Γ(Y, ⊤)))
    (_hInvertX' : IsUnit (N : Γ(X', ⊤))) (_hInvertY' : IsUnit (N : Γ(Y', ⊤)))
    (e : ℕ)
    (_hFib : ∀ y : Y, topologicalKrullDim
      ((CategoryTheory.Limits.pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y)) : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (a b : ℤ)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    (_hK : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) K)
    (_hInterval : pbcReductionsCohomologyIn X (pbcIntegralDatum l E) a b K) :
    PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
      ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
    PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
      (completedPullbackObject g (pbcIntegralDatum l E)
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K)) ∧
    PbcIsBoundedConstructibleComplete X' (pbcIntegralDatum l E)
      (completedPullbackObject g' (pbcIntegralDatum l E) K) ∧
    PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
      ((completedDerivedDirectImage f' (pbcIntegralDatum l E)).obj
        (completedPullbackObject g' (pbcIntegralDatum l E) K)) ∧
    pbcReductionsCohomologyIn X' (pbcIntegralDatum l E) a b
      (completedPullbackObject g' (pbcIntegralDatum l E) K) ∧
    pbcReductionsCohomologyIn Y (pbcIntegralDatum l E) a (b + 2 * (e : ℤ))
      ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
    pbcReductionsCohomologyIn Y' (pbcIntegralDatum l E) a (b + 2 * (e : ℤ))
      (completedPullbackObject g (pbcIntegralDatum l E)
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K)) ∧
    pbcReductionsCohomologyIn Y' (pbcIntegralDatum l E) a (b + 2 * (e : ℤ))
      ((completedDerivedDirectImage f' (pbcIntegralDatum l E)).obj
        (completedPullbackObject g' (pbcIntegralDatum l E) K)) := by
  sorry

end WeilConjectures
