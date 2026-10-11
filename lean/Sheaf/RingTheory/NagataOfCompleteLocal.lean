/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.NagataRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Complete Noetherian local rings are Nagata

Source: Stacks Project, Algebra, Lemma 10.162.8 (Tag 032W)
(blueprint: lem-weil-pbc-complete-local-nagata).
-/

@[expose] public section

universe u

/-- A Noetherian ring complete at its unique maximal ideal is Nagata.
Source: Stacks Project, Algebra, Tag 032W
(blueprint: lem-weil-pbc-complete-local-nagata).

Proof (the six steps of the DAG node):
1. For each prime ideal `p`, the quotient `R / p` is a complete Noetherian local domain
   by `lem-weil-pbc-complete-local-quotient`. It suffices to prove such domains are N-2.
2. By `lem-weil-pbc-complete-local-domain-finite-over-regular`, such a domain is finite
   over a subring isomorphic to a multivariate power series ring over a field or Cohen
   ring. Noetherianity and N-2 are invariant under ring isomorphism: monic equations,
   fraction fields, and module generators transport along the isomorphism. By
   `lem-weil-pbc-n2-ascends-finite-domain-extension`, it suffices that this subring is N-2.
3. Induct on the number of variables using `lem-weil-pbc-power-series-n2`. The zero-variable
   ring is the coefficient ring. Regrouping coefficients by the last coordinate identifies
   the next multivariate ring with a one-variable power series ring over the preceding one;
   the coefficient convolution formula respects this regrouping.
4. A field is Noetherian and N-2: in a finite field extension every element satisfies a
   monic equation, obtained from linear dependence of its powers and division by the
   leading coefficient. Its integral closure is the extension itself, finite by a basis.
5. A Cohen ring is a Noetherian normal domain by `lem-weil-pbc-pid-noetherian-normal`.
   Its residue ring modulo the prime `p` is a field, hence N-2 by step 4; it is complete
   for this principal ideal. Apply `lem-weil-pbc-tate-n2-complete-principal` with `x = p`.
6. Steps 4 and 5 supply the coefficient cases, step 3 supplies their power series rings,
   step 2 supplies the complete local domains, and step 1 shows every prime quotient
   of `R` is N-2. Together with Noetherianity this is `IsNagataRing R`. -/
theorem isNagataRing_of_complete_local (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : IsNagataRing R := by
  sorry
