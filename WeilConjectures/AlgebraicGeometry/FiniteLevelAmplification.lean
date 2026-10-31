/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ConstructibleDirectImageFiniteness

/-!
# Finite-level amplification

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`,
`def-weil-pbc-finite-level-amplification`, clauses (1)--(2) and final interval convention
(blueprint: def-weil-pbc-finite-level-amplification).

The full bounded constructible categories and their operations are the recorded ones.
Restriction to the full subcategory is expressed by preservation of its object predicate;
additivity, shifts and distinguished triangles are inherited from the ambient functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Cohomology lies in the closed interval `[a,b]` when it vanishes in every degree
strictly below `a` or strictly above `b`. This is a predicate on the ambient derived
object and can in particular be applied to its bounded constructible full subcategory.
Source: blueprint `def-weil-pbc-finite-level-amplification`, final paragraph
(blueprint: def-weil-pbc-finite-level-amplification). -/
def finiteCoefficientCohomologyIn (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (a b : ℤ) (K : FiniteCoefficientDerivedCategory T Λ) : Prop :=
  ∀ i : ℤ, (i < a ∨ b < i) →
    IsZero ((DerivedCategory.homologyFunctor (FiniteCoefficientModules T Λ) i).obj K)

/-- The actual derived pullback preserves the bounded constructible full subcategory,
is additive and triangulated for the induced structures, and preserves every ordered
cohomological interval. The commutation with shifts is the canonical one attached to
exact termwise descent, used by `Functor.IsTriangulated`.
Source: blueprint `def-weil-pbc-finite-level-amplification`, clause (2)
(blueprint: def-weil-pbc-finite-level-amplification). -/
def finiteCoefficientPullbackAmplifies {S T : Scheme.{u}} (g : S ⟶ T)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] : Prop :=
  (finiteCoefficientDerivedPullback T Λ g).Additive ∧
  (finiteCoefficientDerivedPullback T Λ g).IsTriangulated ∧
  (∀ K : FiniteCoefficientDerivedCategory T Λ,
    isBoundedConstructibleFiniteCoefficient T Λ K →
      isBoundedConstructibleFiniteCoefficient S Λ
        ((finiteCoefficientDerivedPullback T Λ g).obj K)) ∧
  ∀ (a b : ℤ), a ≤ b → ∀ K : FiniteCoefficientDerivedCategory T Λ,
    isBoundedConstructibleFiniteCoefficient T Λ K →
    finiteCoefficientCohomologyIn T Λ a b K →
      finiteCoefficientCohomologyIn S Λ a b
        ((finiteCoefficientDerivedPullback T Λ g).obj K)

/-- AMP for one chosen Cartesian square and one common nonnegative bound, simultaneously
at every positive quotient exponent. Both direct images satisfy FIN with that same
bound, and both finite-level pullbacks are exact and preserve bounded constructibility
and every interval `[a,b]`. The explicit target and coefficient hypotheses are precisely
the conventions required wherever FIN is used. This defines a property and asserts no
square satisfies it.
Source: blueprint `def-weil-pbc-finite-level-amplification`, clauses (1)--(2)
(blueprint: def-weil-pbc-finite-level-amplification). -/
def HasFiniteLevelAmplification
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (_square : ChosenCartesianSquare g' f' f g)
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (htorsion : IsAddTorsion (A ⧸ I))
    [hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]
    (hperfect : ∀ m : ℕ+,
      @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _)
        ((@DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) _ _
          (HasDerivedCategory.standard _) 0).obj (ModuleCat.of A (A ⧸ I ^ (m : ℕ)))))
    [IsNoetherian Y] [IsNoetherian Y']
    (hDimY : ∃ k : ℕ, topologicalKrullDim Y ≤ (k : WithBot ℕ∞))
    (hDimY' : ∃ k : ℕ, topologicalKrullDim Y' ≤ (k : WithBot ℕ∞))
    (hInvertY : ∀ (n : ℕ+) (a : A ⧸ I ^ (n : ℕ)) (y : Y),
      IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (hInvertY' : ∀ (n : ℕ+) (a : A ⧸ I ^ (n : ℕ)) (y : Y'),
      IsUnit (addOrderOf a : Y'.presheaf.stalk y))
    (c : ℕ) : Prop :=
  ∀ n : ℕ+,
    letI : TopologicalSpace (A ⧸ I ^ (n : ℕ)) := ⊥
    letI : DiscreteTopology (A ⧸ I ^ (n : ℕ)) := ⟨rfl⟩
    ConstructibleDirectImageFiniteness A I hI htorsion hperfect n
      hDimY (hInvertY n) f c ∧
    ConstructibleDirectImageFiniteness A I hI htorsion hperfect n
      hDimY' (hInvertY' n) f' c ∧
    finiteCoefficientPullbackAmplifies g (A ⧸ I ^ (n : ℕ)) ∧
    finiteCoefficientPullbackAmplifies g' (A ⧸ I ^ (n : ℕ))

end AlgebraicGeometry.ProEtale
