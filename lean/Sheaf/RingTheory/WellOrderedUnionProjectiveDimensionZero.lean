/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# zero case of the well-ordered union argument

Source: Stacks Project, Algebra, Lemma 0D1U.
-/

@[expose] public section

universe u v w

namespace ModuleCat

/-- Base case of Auslander's well-ordered union argument.
Source: Stacks Project, Algebra, Lemma 0D1U, the case `n = 0`.
(blueprint: lem-weil-pbc-well-ordered-union-zero-step).

Proof: write `U e` for the supremum of the preceding stages, pulled back into `F e`,
and `Q e = F e / U e`. A length-zero projective resolution makes its augmentation
an isomorphism: its degree-one object is zero and its augmentation is a cokernel
of the zero arrow. Thus each `Q e` is a projective object in `ModuleCat.{v} R`.
The quotient projection `F e → Q e` is an epimorphism. Its projectivity supplies
an R-linear section `s e`. Compose this section with the inclusion into `M`.

Define `psi` from the external direct sum of the `Q e` to `M` by the finite sum
of the section maps. For injectivity take a nonzero vector and the largest index
in its finite nonempty support. Its image lies in that stage; projection to that
stage's quotient kills all smaller components and leaves its nonzero component.
For surjectivity use well-founded induction on a stage containing the given
vector `y`. Subtract `s e` of its quotient class. The difference belongs to the
predecessor supremum. Directedness of the nonempty chain of earlier stages
identifies that supremum with their union. Hence the difference is in an earlier
stage and the induction hypothesis applies. At a least stage the predecessor
is zero, so the difference is zero. Add back the section to obtain a preimage.

The direct sum is consequently linearly equivalent to `M`. If `E` lives in a
larger universe, shrink this direct sum along the equivalence before regarding
it as an object of `ModuleCat.{v} R`. To verify its categorical projectivity,
lift a map out of it across an epimorphism by lifting each component using the
categorical projectivity of `Q e`, and sum the lifts on finite supports. This
argument does not require the ring to be small in universe `v`. Transfer
projectivity to `M` and use the identity resolution, concentrated in degree zero.
No choice is used to define library data: the sections only occur in this proof.

Edge cases: an empty `E` is excluded by `hcover` applied to zero. Repeated stages
have zero successive quotients and contribute zero summands. For a single stage
the quotient projection is the identification with the whole module. -/
theorem hasProjectiveResolutionLE_of_wellOrderedUnion_zero
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (hquot : ∀ e : E, HasProjectiveResolutionLE
      (ModuleCat.of R ((F e) ⧸
        ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) 0) :
    HasProjectiveResolutionLE M 0 := by
  sorry

end ModuleCat
