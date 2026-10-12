/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.RingTheory.LocalRing.Module
import Sheaf.RingTheory.NakayamaNilpotent

/-!
# Lifting bases over a local ring with nilpotent maximal ideal

Source: Stacks Project, Algebra, Lemma 10.101.1, Tag 051F
(blueprint: lem-weil-pbc-local-artinian-basis-when-flat).
-/

@[expose] public section

universe u v w

namespace Module

/-- A family in a flat module over a local ring with nilpotent maximal ideal is a basis
if and only if its reductions form a basis over the residue field. No finite generation
of the module or finiteness of the index type is assumed.

Source: Stacks Project, Algebra, Lemma 10.101.1, Tag 051F
(blueprint: lem-weil-pbc-local-artinian-basis-when-flat).

Proof: Let F be the direct sum of copies of R indexed by A, and let phi : F -> M send each
standard basis vector to x a. Modulo the maximal ideal m, F/mF is the direct sum of copies
of R/m, and the reduced map sends the standard basis to the classes of x a. Thus the two
basis assertions say that the reduced map and phi, respectively, are bijective.
If phi is bijective, it carries mF onto mM and induces the required quotient isomorphism.
Conversely, bijectivity of the reduced map implies surjectivity of phi by Nakayama for a
nilpotent ideal (lem-weil-pbc-nakayama-nilpotent), without a finiteness assumption.
Put K = ker phi. The short exact sequence 0 -> K -> F -> M -> 0
(def-weil-pbc-exact-sequence) stays exact after tensoring with R/m, by flatness of M
(def-weil-pbc-flat-ring-map and lem-weil-pbc-flat-quotient-tensor-injective, Tag 00HL).
The natural identifications (R/m) tensor P = P/mP for P = K, F, M
(lem-weil-pbc-tensor-over-quotient-ring) give an exact sequence of the quotients.
Since the reduced phi is injective, K/mK = 0. Nakayama for the nilpotent ideal again
(lem-weil-pbc-nakayama-nilpotent, applied to 0 -> K) gives K = 0. Therefore phi is also
injective, hence bijective, proving the other basis assertion. -/
theorem basis_iff_basisQuotient_of_nilpotent
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hm : IsNilpotent (IsLocalRing.maximalIdeal R)) {A : Type w} (x : A → M) :
    (∃ b : Basis A (R ⧸ IsLocalRing.maximalIdeal R)
      (M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))),
      ∀ a : A, b a = (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (x a)) ↔
    (∃ b : Basis A R M, ∀ a : A, b a = x a) := by
  sorry

end Module
