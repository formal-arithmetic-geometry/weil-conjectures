/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLevelAmplification
import Sheaf.Paper.RestrictionDirectImage

/-!
# Amplitude containments implied by finite-level amplification

Source: Weil conjectures blueprint, sec-proper-base-change/sk-thm-properbasechange,
order 1351 (blueprint: prop-weil-pbc-amplification-consequences).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Amplification gives all four containments for each positive quotient and each
ordered integer interval. Both ordinary derived direct images preserve bounded
constructibility and enlarge the upper bound by the common nonnegative `c`. Both
ordinary derived pullbacks preserve bounded constructibility and the same interval.

Source: blueprint order 1351
(blueprint: prop-weil-pbc-amplification-consequences).

Proof: fix the positive exponent n. Unfold HasFiniteLevelAmplification to obtain
FIN(f,P_n;c), FIN(f',P_n;c), and the two exact interval-preserving pullback clauses
(def-weil-pbc-finite-level-amplification). Apply
prop-weil-pbc-restriction-direct-image to the first FIN clause, using the definition
of def-weil-pbc-constructible-direct-image-finiteness, to obtain constructibility
and the interval [a,b+c] for Rf_*. Apply the same proposition to the second FIN
clause to obtain the identical bound for Rf'_*. The last two containments are
the constructibility and interval clauses already included in the two pullback
amplification hypotheses. These arguments apply to every ambient object satisfying
the bounded constructible predicate and the indicated cohomology vanishing predicate. -/
theorem finiteLevelAmplification_consequences
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (square : ChosenCartesianSquare g' f' f g)
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (htorsion : IsAddTorsion (A ⧸ I))
    [hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]
    (hperfect : ∀ m : ℕ+,
      @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _)
        ((@DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) _ _
          (HasDerivedCategory.standard _) 0).obj (ModuleCat.of A (A ⧸ I ^ (m : ℕ)))))
    [IsNoetherian Y] [IsNoetherian Y']
    (hDimY : ∃ k : ℕ, topologicalKrullDim Y ≤ k)
    (hDimY' : ∃ k : ℕ, topologicalKrullDim Y' ≤ k)
    (hInvertY : ∀ (n : ℕ+) (a : A ⧸ I ^ (n : ℕ)) (y : Y),
      IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (hInvertY' : ∀ (n : ℕ+) (a : A ⧸ I ^ (n : ℕ)) (y : Y'),
      IsUnit (addOrderOf a : Y'.presheaf.stalk y))
    (c : ℕ)
    (hAmp : HasFiniteLevelAmplification g' f' f g square A I hI htorsion hperfect
      hDimY hDimY' hInvertY hInvertY' c)
    (n : ℕ+) [TopologicalSpace (A ⧸ I ^ (n : ℕ))]
    [DiscreteTopology (A ⧸ I ^ (n : ℕ))] (a b : ℤ) (hab : a ≤ b) :
    (∀ K : FiniteCoefficientDerivedCategory X (A ⧸ I ^ (n : ℕ)),
      isBoundedConstructibleFiniteCoefficient X (A ⧸ I ^ (n : ℕ)) K →
      finiteCoefficientCohomologyIn X (A ⧸ I ^ (n : ℕ)) a b K →
        isBoundedConstructibleFiniteCoefficient Y (A ⧸ I ^ (n : ℕ))
          ((finiteCoefficientDerivedDirectImage f (A ⧸ I ^ (n : ℕ))).obj K) ∧
        finiteCoefficientCohomologyIn Y (A ⧸ I ^ (n : ℕ)) a (b + (c : ℤ))
          ((finiteCoefficientDerivedDirectImage f (A ⧸ I ^ (n : ℕ))).obj K)) ∧
    (∀ K : FiniteCoefficientDerivedCategory X' (A ⧸ I ^ (n : ℕ)),
      isBoundedConstructibleFiniteCoefficient X' (A ⧸ I ^ (n : ℕ)) K →
      finiteCoefficientCohomologyIn X' (A ⧸ I ^ (n : ℕ)) a b K →
        isBoundedConstructibleFiniteCoefficient Y' (A ⧸ I ^ (n : ℕ))
          ((finiteCoefficientDerivedDirectImage f' (A ⧸ I ^ (n : ℕ))).obj K) ∧
        finiteCoefficientCohomologyIn Y' (A ⧸ I ^ (n : ℕ)) a (b + (c : ℤ))
          ((finiteCoefficientDerivedDirectImage f' (A ⧸ I ^ (n : ℕ))).obj K)) ∧
    (∀ K : FiniteCoefficientDerivedCategory Y (A ⧸ I ^ (n : ℕ)),
      isBoundedConstructibleFiniteCoefficient Y (A ⧸ I ^ (n : ℕ)) K →
      finiteCoefficientCohomologyIn Y (A ⧸ I ^ (n : ℕ)) a b K →
        isBoundedConstructibleFiniteCoefficient Y' (A ⧸ I ^ (n : ℕ))
          ((finiteCoefficientDerivedPullback Y (A ⧸ I ^ (n : ℕ)) g).obj K) ∧
        finiteCoefficientCohomologyIn Y' (A ⧸ I ^ (n : ℕ)) a b
          ((finiteCoefficientDerivedPullback Y (A ⧸ I ^ (n : ℕ)) g).obj K)) ∧
    (∀ K : FiniteCoefficientDerivedCategory X (A ⧸ I ^ (n : ℕ)),
      isBoundedConstructibleFiniteCoefficient X (A ⧸ I ^ (n : ℕ)) K →
      finiteCoefficientCohomologyIn X (A ⧸ I ^ (n : ℕ)) a b K →
        isBoundedConstructibleFiniteCoefficient X' (A ⧸ I ^ (n : ℕ))
          ((finiteCoefficientDerivedPullback X (A ⧸ I ^ (n : ℕ)) g').obj K) ∧
        finiteCoefficientCohomologyIn X' (A ⧸ I ^ (n : ℕ)) a b
          ((finiteCoefficientDerivedPullback X (A ⧸ I ^ (n : ℕ)) g').obj K)) := by
  cases DiscreteTopology.eq_bot (α := A ⧸ I ^ (n : ℕ))
  obtain ⟨hfin, hfin', hpull, hpull'⟩ := hAmp n
  obtain ⟨hconstructible, _, hinterval⟩ :=
    restrictionDirectImage A I hI htorsion hperfect n hDimY (hInvertY n) f c hfin
  obtain ⟨hconstructible', _, hinterval'⟩ :=
    restrictionDirectImage A I hI htorsion hperfect n hDimY' (hInvertY' n) f' c hfin'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK hdegrees
    exact ⟨hconstructible ⟨K, hK⟩, hinterval ⟨K, hK⟩ a b hdegrees⟩
  · intro K hK hdegrees
    exact ⟨hconstructible' ⟨K, hK⟩, hinterval' ⟨K, hK⟩ a b hdegrees⟩
  · intro K hK hdegrees
    exact ⟨hpull.2.2.1 K hK, hpull.2.2.2 a b hab K hK hdegrees⟩
  · intro K hK hdegrees
    exact ⟨hpull'.2.2.1 K hK, hpull'.2.2.2 a b hab K hK hdegrees⟩

end AlgebraicGeometry.ProEtale
