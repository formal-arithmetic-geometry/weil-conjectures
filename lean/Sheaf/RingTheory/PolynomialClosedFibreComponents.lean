/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.CompleteLocalExcellent
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Components of polynomial localizations over a closed point

Source: Stacks Project, More on Algebra, Tag 0AW5, lemma-formally-catenary,
last two proof paragraphs (blueprint: lem-per-polynomial-closed-fibre-components).
-/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry

namespace MvPolynomial

/-- A polynomial localization over the closed point of a complete Noetherian local
ring with equidimensional spectrum is catenary and has equidimensional spectrum;
each component has dimension `dim C + r`.

Source: Stacks Project, More on Algebra, Tag 0AW5, lemma-formally-catenary,
last two proof paragraphs (blueprint: lem-per-polynomial-closed-fibre-components).

Proof (the eight steps of the node):
1. Put P = C[x_1,...,x_r] and D = P localized at M. By
   lem-weil-pbc-finite-type-algebra-noetherian, P is Noetherian. Every ideal of D
   is extended from its contraction to P, so finite generation descends to D.
   By def-weil-pbc-localization-at-prime, D is local with maximal ideal MD.
2. By lem-per-complete-local-excellence and def-exc-excellent-ring, C is universally
   catenary. Hence P is catenary. Prime intervals in D are exactly the intervals
   between primes of P contained in M; all intermediate primes remain contained
   in M. Thus chain bounds and saturated-chain lengths pass to D.
3. For a minimal prime q of D, contract to Q in P. By
   lem-weil-pbc-prime-contains-minimal-prime choose a minimal prime p of C below
   the contraction of Q. Coefficient reduction identifies P/pP with (C/p)[x], a
   domain (the leading coefficient of a product is nonzero). Thus pP is prime
   and contained in Q, and pD is prime and contained in q. Minimality gives q = pD.
4. Put R = C/p, T = R[x], m = n/p, and N = M/pP. The ring R is local, N is
   maximal and contracts to m, and R and T are Noetherian by the finite-type
   Noetherian lemma. Reduction of coefficients in fractions gives D/q = T_N:
   every denominator lifts outside M and the kernel is exactly pD.
5. The monomial basis gives, for every R-module E, E tensor_R T = direct sum E
   indexed by monomials. The map takes a tensor to its coefficient family; its
   inverse sums tensors with the corresponding monomials. Tensoring an injection
   acts coefficientwise, hence remains injective. This proves flatness by
   def-weil-pbc-flat-ring-map.
6. Put k = R/m and N_0 = N/mT. Coefficient reduction in fractions identifies the
   closed fibre of T_N with k[x_1,...,x_r] localized at the maximal ideal N_0.
   By lem-weil-pbc-polynomial-ring-maximal-localization-dimension its dimension
   is r, also for nonrational closed points.
7. Apply lem-weil-pbc-flat-height-formula to the flat map R -> T at N over m.
   Since R_m = R, this gives dim(T_N) = dim(R) + r. Consequently
   dim(D/q) = dim(C/p) + r.
8. By lem-weil-pbc-spec-irreducible-components-minimal-primes, components are
   V(p), homeomorphic to Spec(C/p); by
   lem-weil-pbc-spec-topological-krull-dimension-ring their dimensions are
   dim(C/p). Equidimensionality of Spec(C) makes these equal to dim(C): every
   prime chain lies above a minimal prime, by the minimal-prime existence lemma.
   Apply the same component correspondence to D and step 7. Every component has
   dimension dim(C) + r; hence any two components have equal dimension. -/
theorem isCatenaryRing_equidimensional_localizationAtMaximal
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (heq : ∀ (Z W : Set (Spec (.of C))),
      Z ∈ irreducibleComponents (Spec (.of C)) →
      W ∈ irreducibleComponents (Spec (.of C)) →
      topologicalKrullDim Z = topologicalKrullDim W)
    (r : ℕ) (M : Ideal (MvPolynomial (Fin r) C)) [M.IsMaximal]
    (hclosed : M.comap (MvPolynomial.C : C →+* MvPolynomial (Fin r) C) =
      IsLocalRing.maximalIdeal C) :
    IsCatenaryRing (Localization.AtPrime M) ∧
    (∀ (Z W : Set (Spec (.of (Localization.AtPrime M)))),
      Z ∈ irreducibleComponents (Spec (.of (Localization.AtPrime M))) →
      W ∈ irreducibleComponents (Spec (.of (Localization.AtPrime M))) →
      topologicalKrullDim Z = topologicalKrullDim W) ∧
    (∀ (Z : Set (Spec (.of (Localization.AtPrime M)))),
      Z ∈ irreducibleComponents (Spec (.of (Localization.AtPrime M))) →
      topologicalKrullDim Z = ringKrullDim C + (r : WithBot ℕ∞)) := by
  sorry

end MvPolynomial
