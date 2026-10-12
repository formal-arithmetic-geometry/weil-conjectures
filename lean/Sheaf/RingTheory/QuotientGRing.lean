/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.RingTheory.LocalCompletionQuotient
import Sheaf.RingTheory.RegularBaseChange

/-!
# Quotients of G-rings

Source: Stacks Project, More on Algebra, Lemma 07PP, item (3), specialized to a quotient
map (blueprint: lem-weil-pbc-g-ring-quotient).
-/

@[expose] public section

universe u

/-- A quotient of a G-ring by any ideal is a G-ring. Source: Stacks Project, More on Algebra,
Lemma 07PP, item (3) (blueprint: lem-weil-pbc-g-ring-quotient).

Proof:
1. Put `S = R / I`. It is Noetherian by lem-weil-pbc-finite-type-algebra-noetherian.
   For a prime `pbar` of `S`, its inverse image `p` under the quotient map is prime and
   contains `I` (def-weil-pbc-g-ring).
2. Set `A = R_p`, with maximal ideal `m`, and `J = I A`. By
   lem-weil-pbc-flat-local-ring-maps, `A` is Noetherian local. By
   lem-weil-pbc-localization-at-prime-of-quotient, the map `A → S_pbar` is surjective,
   has kernel `J`, and maps `m` onto the maximal ideal of `S_pbar`
   (def-weil-pbc-localization-at-prime).
3. The completion map of `A` is regular by def-weil-pbc-g-ring. Base change along the
   finite type surjection `A → S_pbar` is regular by lem-weil-pbc-regular-base-change.
4. By lem-weil-pbc-tensor-quotient-base-change, its target is the quotient of the
   completion of `A` by the extended ideal `J`. By lem-weil-pbc-local-completion-quotient,
   this quotient is the completion of `S_pbar`; the isomorphism identifies the base change
   map with the canonical completion map (def-weil-pbc-adic-completion).
5. Transport flatness and geometric regularity of the fibres through this algebra
   isomorphism. The completion map of `S_pbar` is therefore regular. Since `pbar` was
   arbitrary and `S` is Noetherian, def-weil-pbc-g-ring gives the conclusion.
-/
theorem isGRing_quotient {R : Type u} [CommRing R] (hR : IsGRing R) (I : Ideal R) :
    IsGRing (R ⧸ I) := by
  sorry
