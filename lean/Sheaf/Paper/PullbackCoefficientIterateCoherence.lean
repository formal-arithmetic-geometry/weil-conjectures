/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Endomorphism
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Pullback comparisons and coefficient-map iterates

Source: the blueprint, `sec-trace-formula/sk-i-global-additivity`,
`prop-trf-trace-additivity-open-closed.proof.md`, Steps 1 and 6; Stacks Project,
Tags 03D8 and 0D6D (blueprint: lem-trf-pullback-coefficient-iterate-coherence).

The helper declarations render the powers, comparisons and recursion explicitly
introduced by this node; the main theorem states its two displayed identities.

The powers below are powers of scheme endomorphisms, not powers of a chosen pullback
functor. At exponent zero the comparisons are the canonical unital comparisons for
pullback of the identity morphism. Positive coefficient iterates are indexed by `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Powers of a commuting square still commute.
Source: blueprint, trace additivity proof, Step 1
(blueprint: lem-trf-pullback-coefficient-iterate-coherence).
Proof: for exponent zero use the identity laws. For the successor, write each power
as its preceding power followed by the endomorphism. Reassociate, use the original
square, then the induction hypothesis, and reassociate back. This is Step 5 of the
node's proof, before applying the pullback-composition comparisons. -/
theorem trf_commuting_endomorphism_powers {W X : Scheme.{u}} (h : W ⟶ X)
    (tW : W ⟶ W) (t : X ⟶ X) (w : tW ≫ h = h ≫ t) (m : ℕ) :
    ((End.of tW) ^ m : W ⟶ W) ≫ h = h ≫ ((End.of t) ^ m : X ⟶ X) := by
  sorry

/-- The canonical comparison around an arbitrary commuting square, with no Cartesian
assumption. It is the two recorded composition comparisons joined by transport along
the equality of composite scheme morphisms.
Source: blueprint, trace additivity proof, Step 1; Stacks Tag 0D6D
(blueprint: lem-trf-pullback-coefficient-iterate-coherence). -/
def trfPullbackSquareComparison (A : Type u) [CommRing A]
    {W X : Scheme.{u}} (h : W ⟶ X) (a : W ⟶ W) (b : X ⟶ X)
    (w : a ≫ h = h ≫ b) :
    proEtaleConstantRingDerivedPullback A h ⋙ proEtaleConstantRingDerivedPullback A a ≅
      proEtaleConstantRingDerivedPullback A b ⋙ proEtaleConstantRingDerivedPullback A h :=
  proEtaleConstantRingPullbackComposition a h A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) w) ≪≫
    (proEtaleConstantRingPullbackComposition h b A).symm

/-- The specified comparison `d_m : P_(m+1) ≅ P_1 P_m`, including the canonical
identity comparison at `m = 0`. The only transport is the standard power equality.
Source: blueprint, trace additivity proof, Step 1; Stacks Tag 0D6D
(blueprint: lem-trf-pullback-coefficient-iterate-coherence). -/
def trfPullbackPowerStep (A : Type u) [CommRing A] {X : Scheme.{u}}
    (t : X ⟶ X) (m : ℕ) :
    proEtaleConstantRingDerivedPullback A ((End.of t) ^ (m + 1)) ≅
      proEtaleConstantRingDerivedPullback A ((End.of t) ^ m) ⋙
        proEtaleConstantRingDerivedPullback A t :=
  eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) (pow_succ (End.of t) m)) ≪≫
    (proEtaleConstantRingPullbackComposition t ((End.of t) ^ m) A).symm

/-- The coefficient morphism `u_(n+1)`, with `u_1 = u` after the canonical transport
along `t^1 = t`, and `u_(m+1) = u ∘ P_1(u_m) ∘ d_m` thereafter.
Source: blueprint, trace additivity proof, Steps 1 and 6
(blueprint: lem-trf-pullback-coefficient-iterate-coherence). -/
def trfCoefficientIterate (A : Type u) [CommRing A] {X : Scheme.{u}}
    (t : X ⟶ X) (K : proEtaleDerivedCategory X A)
    (f : (proEtaleConstantRingDerivedPullback A t).obj K ⟶ K) :
    (n : ℕ) → (proEtaleConstantRingDerivedPullback A ((End.of t) ^ (n + 1))).obj K ⟶ K
  | 0 => (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
      (pow_one (End.of t)))).hom.app K ≫ f
  | n + 1 => (trfPullbackPowerStep A t (n + 1)).hom.app K ≫
      (proEtaleConstantRingDerivedPullback A t).map (trfCoefficientIterate A t K f n) ≫ f

/-- Canonical pullback comparisons satisfy the cocycle for every nonnegative exponent
and intertwine every positive coefficient iterate, without any invertibility,
finite-type, or Cartesian-square hypothesis.
Source: blueprint, trace additivity proof, Steps 1 and 6; Stacks Tags 03D8, 0B65,
0DV0 and 0D6D (blueprint: lem-trf-pullback-coefficient-iterate-coherence).

Proof (the six steps of the node):
1. The direct-image composition maps are the fibre-product pasting maps. Their
   associativity and units follow from their two projections. Their constant-ring
   maps send each constant to itself, so the scalar identifications also compose.
2. Use the composite adjunction and conjugate-iso unit equation to characterize
   the ordinary module pullback comparisons uniquely. On tensors the forward map
   inserts a scalar unit, and the inverse multiplies scalars; balancing verifies
   the normalization and inverse identities.
3. Both triple comparisons transpose to the same three successive units. The
   conjugate-iso uniqueness gives associativity, and the identity adjunction gives
   the unit laws, on all module sheaves.
4. Exact termwise pullback descends through localization. The localization universal
   property preserves composition and is faithful on natural transformations, so
   associativity and units descend. On flat K-flat resolutions these are exactly
   the comparisons of the recorded composition lemma; naturality across the
   resolution quasi-isomorphism identifies them on every derived object.
5. The commuting-power equality follows by induction. Apply associativity to the
   triples `(h,t,t^m)`, `(tW,h,t^m)` and `(tW,tW^m,h)`, substitute the commuting
   equalities, and cancel the two inverse composition comparisons. This gives the
   first displayed identity, including exponent zero by the unit laws.
6. Induct on the positive coefficient exponent. The first case is the definition
   of the pulled-back coefficient map. In the successor step expand the recursion,
   use naturality of `c_1` at the preceding iterate, then the first identity and
   functoriality of pullback. No inverse of the coefficient morphism is used. -/
theorem trf_pullback_coefficient_iterate_coherence (A : Type u) [CommRing A] [Finite A]
    {W X : Scheme.{u}} (h : W ⟶ X) (tW : W ⟶ W) (t : X ⟶ X)
    (w : tW ≫ h = h ≫ t) (K : proEtaleDerivedCategory X A) :
    (∀ m : ℕ,
      (trfPullbackSquareComparison A h ((End.of tW) ^ (m + 1))
        ((End.of t) ^ (m + 1)) (trf_commuting_endomorphism_powers h tW t w (m + 1))).hom.app K ≫
          (proEtaleConstantRingDerivedPullback A h).map ((trfPullbackPowerStep A t m).hom.app K) =
        (trfPullbackPowerStep A tW m).hom.app
            ((proEtaleConstantRingDerivedPullback A h).obj K) ≫
          (proEtaleConstantRingDerivedPullback A tW).map
            ((trfPullbackSquareComparison A h ((End.of tW) ^ m) ((End.of t) ^ m)
              (trf_commuting_endomorphism_powers h tW t w m)).hom.app K) ≫
          (trfPullbackSquareComparison A h tW t w).hom.app
            ((proEtaleConstantRingDerivedPullback A ((End.of t) ^ m)).obj K)) ∧
      (∀ (f : (proEtaleConstantRingDerivedPullback A t).obj K ⟶ K) (n : ℕ),
        trfCoefficientIterate A tW ((proEtaleConstantRingDerivedPullback A h).obj K)
            ((trfPullbackSquareComparison A h tW t w).hom.app K ≫
              (proEtaleConstantRingDerivedPullback A h).map f) n =
          (trfPullbackSquareComparison A h ((End.of tW) ^ (n + 1))
              ((End.of t) ^ (n + 1))
              (trf_commuting_endomorphism_powers h tW t w (n + 1))).hom.app K ≫
            (proEtaleConstantRingDerivedPullback A h).map (trfCoefficientIterate A t K f n)) := by
  sorry

end AlgebraicGeometry.Scheme
