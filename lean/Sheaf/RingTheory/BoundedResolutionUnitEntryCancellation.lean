module

public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Sheaf.Algebra.Homology.UnitEntrySplits

/-!
# Cancellation at a supplied unit entry in a bounded free resolution

Source: Stacks Project, Algebra, Tag 00MT, used in the proof of Tag 00OA.
(blueprint: stage3-j4-bounded-resolution-unit-entry-cancellation)
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat

/-- Remove a supplied unit pivot, preserving the augmentation and controlling ranks.
Source: Stacks Project, Algebra, Tag 00MT, used in the proof of Tag 00OA.

Proof: Extend the natural-degree complex by zero to negative integer degrees;
use the supplied bases in nonnegative degrees and the empty basis in negative
ones. Apply `ChainComplex.exists_splitting_of_isUnit_entry` in degree `j + 1`
with the supplied pivot. Restrict its complementary complex to natural degrees.
The identity summand occupies degrees `j + 1` and `j`, both at most `d`.
It is contractible, with homotopy the inverse of its identity differential.
The augmentation kills it: if `j = 0`, its degree-zero term is the image of
its degree-one differential, and the augmentation composed with that differential
is zero; if `j > 0`, its degree-zero term is zero. Restrict the augmentation
along the inclusion of the complement. The inclusion induces isomorphisms on
homology because the other summand is contractible. Its composite augmentation
therefore is a quasi-isomorphism onto the single complex on `M`, as is the
original augmentation. The complementary terms have bases supplied by the
splitting theorem and hence are finite free and projective, so these data form
`P' : ProjectiveResolution M`. Outside the two pivot degrees the bases have
size `n i`, while in the pivot degrees their sizes plus one equal `n i`.
Invariant basis number over the nontrivial commutative ring identifies these
sizes with finrank. Thus ranks never increase, and at `j` they strictly drop.
Above `d` the complement is a direct summand of the original zero module, so
it is zero. No local-ring criterion or choice of a unit pivot is part of this
statement: the pivot and its invertibility are inputs.
(blueprint: stage3-j4-bounded-resolution-unit-entry-cancellation) -/
theorem exists_bounded_resolution_unit_entry_cancellation {R : Type u} [CommRing R]
    [Nontrivial R] (M : ModuleCat.{max u v} R) (d : ℕ) (P : ProjectiveResolution M)
    (hzero : ∀ i : ℕ, d < i → IsZero (P.complex.X i))
    (n : ℕ → ℕ) (b : ∀ i : ℕ, Module.Basis (Fin (n i)) R (P.complex.X i))
    (j : ℕ) (hjd : j < d) (p : Fin (n (j + 1))) (q : Fin (n j))
    (hu : IsUnit (LinearMap.toMatrix (b (j + 1)) (b j)
      (P.complex.d (j + 1) j).hom q p)) :
    ∃ P' : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (P'.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (P'.complex.X i) ∧ Module.Free R (P'.complex.X i)) ∧
      (∀ i : Fin (d + 1), Module.finrank R (P'.complex.X i.val) ≤
        Module.finrank R (P.complex.X i.val)) ∧
      Module.finrank R (P'.complex.X j) < Module.finrank R (P.complex.X j) := by
  sorry

end ModuleCat
