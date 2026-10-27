/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.CompleteLocalExcellence
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Components of a polynomial localization over a complete local ring

Source: Stacks Project, More on Algebra, Tag 0AW5, lemma-formally-catenary,
last two proof paragraphs (blueprint: lem-per-polynomial-closed-fibre-components).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

/-- A polynomial ring over a complete equidimensional Noetherian local ring, localized
at a maximal ideal over the closed point, is catenary and equidimensional. Each component
has dimension `dim C + r`.

Source: Stacks Project, More on Algebra, Tag 0AW5, lemma-formally-catenary,
last two proof paragraphs (blueprint: lem-per-polynomial-closed-fibre-components).

Proof:
1. Put P = C[x_1,...,x_r] and D = P_M. By
   `lem-weil-pbc-finite-type-algebra-noetherian`, P is Noetherian. Every ideal of D is
   extended from its contraction to P: multiplying a fraction in the ideal by its
   denominator puts its numerator in the contraction. Thus D is Noetherian and local,
   by `def-weil-pbc-localization-at-prime`.
2. By `lem-per-complete-local-excellence` and `def-exc-excellent-ring`, C is universally
   catenary, so P is catenary. Extension and contraction identify prime intervals of D
   with prime intervals of P contained in M, preserving chains and saturation. Thus D
   is catenary.
3. For a minimal prime q of D, contract it to Q in P. By
   `lem-weil-pbc-prime-contains-minimal-prime`, choose a minimal prime p of C below the
   contraction of Q to C. Coefficient reduction gives P/pP = (C/p)[x_1,...,x_r], a domain
   (the leading monomial of a product has nonzero coefficient). Hence pP is prime and
   lies below Q and M. Minimality of q gives q = pD.
4. Put R = C/p and T = R[x_1,...,x_r], and let N be the image of M in T. Coefficient
   reduction on fractions gives D/q = T_N: denominators lift outside M, and the kernel
   consists precisely of fractions in pD. R and T are Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`; R is local and N lies over its maximal
   ideal m. These identifications use `def-weil-pbc-mv-polynomial-ring` and
   `def-weil-pbc-localization-at-prime`.
5. The map R → T is flat by `def-weil-pbc-flat-ring-map`: for any R-module L, the
   monomial coefficients identify L ⊗ T with a direct sum of copies of L. The inverse
   sends a finitely supported family to the sum of its entries tensored with monomials.
   Tensoring an injection is therefore injective on every coefficient.
6. The closed fibre of T_N is k[x_1,...,x_r] localized at the image of N, where k = R/m.
   Coefficient reduction on fractions proves this identification, since denominators
   lift outside N and the kernel is mT_N. This image is maximal, and
   `lem-weil-pbc-polynomial-ring-maximal-localization-dimension` gives dimension r,
   including non-rational closed points.
7. Apply `lem-weil-pbc-flat-height-formula` to R → T at N: dim T_N = dim R_m + r.
   Since R is local, R_m = R. Step 4 gives dim(D/q) = dim(C/p) + r.
8. By `lem-weil-pbc-spec-irreducible-components-minimal-primes` and
   `lem-weil-pbc-spec-topological-krull-dimension-ring`, the component V(p) has dimension
   dim(C/p). Equidimensionality of Spec C makes this dim C: every prime chain lies over
   a minimal prime by `lem-weil-pbc-prime-contains-minimal-prime`, so the dimension of
   the spectrum is the supremum of the component dimensions. The same correspondence
   for D identifies each component with Spec(D/q). Step 7 gives dimension dim C + r
   for every component, proving equidimensionality as well as the stated dimension.
-/
theorem isCatenaryRing_equidimensional_localizationAtMaximal
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (hequidim : ∀ Z ∈ irreducibleComponents (AlgebraicGeometry.Spec (CommRingCat.of C)),
      ∀ W ∈ irreducibleComponents (AlgebraicGeometry.Spec (CommRingCat.of C)),
        topologicalKrullDim Z = topologicalKrullDim W)
    (r : ℕ) (M : Ideal (MvPolynomial (Fin r) C)) [M.IsMaximal]
    (hclosed : M.comap (MvPolynomial.C : C →+* MvPolynomial (Fin r) C) =
      IsLocalRing.maximalIdeal C) :
    IsCatenaryRing (Localization.AtPrime M) ∧
      (∀ Z ∈ irreducibleComponents
          (AlgebraicGeometry.Spec (CommRingCat.of (Localization.AtPrime M))),
        ∀ W ∈ irreducibleComponents
          (AlgebraicGeometry.Spec (CommRingCat.of (Localization.AtPrime M))),
            topologicalKrullDim Z = topologicalKrullDim W) ∧
      (∀ Z ∈ irreducibleComponents
          (AlgebraicGeometry.Spec (CommRingCat.of (Localization.AtPrime M))),
        topologicalKrullDim Z = ringKrullDim C + (r : WithBot ℕ∞)) := by
  sorry

end MvPolynomial
