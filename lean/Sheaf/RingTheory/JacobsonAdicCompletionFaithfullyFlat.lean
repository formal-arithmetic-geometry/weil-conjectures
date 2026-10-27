module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Faithful flatness of completion inside the Jacobson radical

Source: Stacks Project, Algebra, Tag 00MC, `lemma-completion-faithfully-flat`
(blueprint: lem-per-jacobson-adic-completion-faithfully-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

/-- The canonical algebra map to the adic completion is faithfully flat when the ring is
Noetherian and the ideal lies in its Jacobson radical. The algebra structure is Mathlib's
canonical one: an element maps to its residue classes modulo the powers of the ideal.
The coordinate at zero is the unique element of `R / R`, so the compatible families indexed
by natural numbers describe the same limit as those indexed by positive integers.

Source: Stacks Project, Algebra, Tag 00MC, `lemma-completion-faithfully-flat`
(blueprint: lem-per-jacobson-adic-completion-faithfully-flat).

Proof:
1. By `lem-weil-pbc-noetherian-completion-flat`, namely
   `AdicCompletion.flat_of_isNoetherian`, the completion is flat over `R` for every ideal `I`.
2. For each maximal ideal `m`, the Jacobson-radical hypothesis implies `I ≤ m`. Compose
   `AdicCompletion.evalOneₐ I` with the quotient map `R / I → R / m`. The resulting ring map
   sends every finite sum of products of images of elements of `m` with completion elements
   to zero. Thus the extended ideal `m` cannot contain one, since `R / m` is nonzero.
3. Apply `lem-weil-pbc-flat-faithfully-flat-maximal-ideals`, namely
   `Module.faithfullyFlat_iff`, to the flatness from step 1 and the properness from step 2.
-/
theorem faithfullyFlat_of_le_jacobson
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson) :
    Module.FaithfullyFlat R (AdicCompletion I R) := by
  sorry

end AdicCompletion
