/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ComparisonDirectImage

/-!
# Finiteness of proper direct images

Source: Weil blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1304;
SGA 4 1/2, Theoreme de finitude, Theorem 1.1; Stacks Tags 095U and 0GL0
(blueprint: thm-weil-pbc-direct-image-finiteness-proper).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Proper direct-image finiteness for Lambda = A/I^n, with the specified bound 2e.
The coefficient hypotheses are those of the adic datum: Noetherianity of A, finite
generation of I, additive torsion of A/I, and finiteness and perfectness of every
positive quotient over A. The positive index n fixes Lambda. No completeness of A
is assumed. The conclusion uses the recorded finite-coefficient FIN predicate.
Source: blueprint order 1304; SGA 4 1/2, finitude 1.1; Stacks Tags 095U and 0GL0
(blueprint: thm-weil-pbc-direct-image-finiteness-proper).

Proof:
1. For a constructible pro-etale F, choose its constructible etale origin G using
   def-weil-pbc-constructible-direct-image-finiteness. The finite ring A/I^n is killed
   by the positive additive order of 1: N m = (N 1)m = 0. Thus G is torsion.
   The coefficient orders are invertible on Y by hypothesis. Apply
   lem-weil-pbc-etale-proper-direct-image-finiteness: all nonnegative higher direct
   images of G are constructible and those in degrees above 2e vanish.
2. Properness gives finite type and separatedness, hence quasi-compactness and a
   quasi-compact diagonal (a closed immersion), so f is quasi-separated, as in
   def-weil-pbc-scheme-conventions and def-weil-closed-immersion. Apply
   prop-weil-pbc-comparison-direct-image to G in degree zero. By
   prop-weil-pbc-site-comparison-finite-level, comparison inverse image is exact;
   it preserves kernels, images and their quotients, hence commutes with cohomology.
   Consequently R^q f_* F is isomorphic to the comparison pullback of R^q f_* G.
   The latter is of constructible etale origin and is zero for q > 2e.
   These are precisely the two clauses of FIN(f,Lambda;2e), uniformly in F. -/
theorem constructibleDirectImageFiniteness_of_isProper
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (htorsion : IsAddTorsion (A ⧸ I))
    [hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]
    (hperfect : ∀ m : ℕ+,
      @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _)
        ((@DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) _ _
          (HasDerivedCategory.standard _) 0).obj (ModuleCat.of A (A ⧸ I ^ (m : ℕ)))))
    (n : ℕ+)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hXdim : ∃ k : ℕ, topologicalKrullDim X ≤ (k : WithBot ℕ∞))
    (hYdim : ∃ k : ℕ, topologicalKrullDim Y ≤ (k : WithBot ℕ∞))
    (hXorders : ∀ (a : A ⧸ I ^ (n : ℕ)) (x : X),
      IsUnit (addOrderOf a : X.presheaf.stalk x))
    (hYorders : ∀ (a : A ⧸ I ^ (n : ℕ)) (y : Y),
      IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (hfib : ∀ y : Y,
      topologicalKrullDim ↥(pullback f (Y.algClosurePoint y)) ≤ (e : WithBot ℕ∞)) :
    ConstructibleDirectImageFiniteness A I hI htorsion hperfect n
      hYdim hYorders f (2 * e) := by
  sorry

end AlgebraicGeometry.ProEtale
