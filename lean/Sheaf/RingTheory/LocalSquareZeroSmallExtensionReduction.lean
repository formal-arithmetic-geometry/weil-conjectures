module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # From small Artinian extensions to local square-zero tests

Source: Stacks Project, More on Algebra, Tag 0DYG, proof of (3) implies (2);
Algebra, Definition 02HS (blueprint: lem-sfb-local-square-zero-small-extension-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- Small Artinian extension tests with fixed residue field imply lifting over local
square-zero extensions with nilpotent maximal ideal. The ring `A` need not be Artinian
or Noetherian. Length one is exactly the small-extension kernel condition of Stacks 02HS:
the kernel is nonzero, killed by the maximal ideal, and one-dimensional over the residue
field. The local structure on `A ⧸ J` is uniquely determined and exists because `J² = 0`.

Source: Stacks Project, More on Algebra, Tag 0DYG, (3) implies (2), and Algebra, Tag 02HS
(blueprint: lem-sfb-local-square-zero-small-extension-reduction).

Proof:
1. Filter `J` by `m_A^t J`, for `0 ≤ t ≤ N`. The successive kernels are square-zero
   and killed by the maximal ideal. Quotients and lifts retain locality and the residue
   isomorphism: an inverse modulo a square-zero ideal lifts using `(1+j)(1-j)=1`.
   Thus it suffices to treat `m_A J = 0`; the case `J = 0` is immediate.
2. Put `D = v(S)` and let `C` be its inverse image in `A`. The kernel `L` of `S → D`
   satisfies `n^N ≤ L ≤ n`. By lem-weil-pbc-noetherian-local-quotient-artinian-local,
   `D ≃ S/L` is Artinian local. The inverse-lifting formula makes `C` local with the
   same residue field `k` and nilpotent maximal ideal. Its structure map is local and
   its maximal ideal kills `J`. A lift into `C` will solve the original problem.
3. Consider all hyperplanes `H` in the `k`-vector space `J`. By
   lem-trf-vector-subspace-complement, a nonzero vector has a complementary hyperplane.
   Thus these hyperplanes separate points and form a nonempty family if `J ≠ 0`.
4. Each `C/H → D` is a small extension. Its source is Artinian: in a descending chain
   of ideals, the images in `D` and intersections with the one-dimensional kernel
   stabilize; equality of both implies equality of nested ideals. Apply the assumed
   test to obtain a lift `f_H : S → C/H` for every `H`.
5. Form the subring `P` of the product of the `C/H` consisting of tuples with the same
   image in `D`. The diagonal `i : C → P` is injective since the hyperplanes separate
   `J`. The kernel `J'` of `P → D` is the product of the `J/H`, with square zero and
   the common residue scalar action. The lifts `f_H` assemble to an R-algebra map to P.
6. Choose a vector-space complement `M` to `i(J)` in `J'` by
   lem-trf-vector-subspace-complement. It is an ideal because the action is by residue
   scalars. Every element of `P` has a unique expression `i(c)+m`, with `m ∈ M`.
   Projection onto `c` is a unital R-algebra retraction `P → C` over `D`. Compose the
   assembled lift with this retraction and `C → A`. Finally iterate along step 1.
-/
theorem local_square_zero_lifting_of_small_artinian_tests
    (R : Type u) (S : Type v)
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hlift : ∀ (B' B : Type (max u v w))
      [CommRing B'] [IsLocalRing B'] [IsArtinianRing B'] [Algebra R B']
      [IsLocalHom (algebraMap R B')]
      [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra R B]
      (p : B' →ₐ[R] B), Function.Surjective p →
      Module.length B' (RingHom.ker p.toRingHom) = 1 →
      ∀ (g : S →ₐ[R] B) [IsLocalHom g.toRingHom],
        Function.Bijective (IsLocalRing.ResidueField.map g.toRingHom) →
        ∃ g' : S →ₐ[R] B', p.comp g' = g)
    (A : Type w) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (N : ℕ) (hN : 1 ≤ N) (hnil : IsLocalRing.maximalIdeal A ^ N = ⊥)
    (J : Ideal A) (hJ : J ^ 2 = ⊥) [IsLocalRing (A ⧸ J)]
    (v : S →ₐ[R] A ⧸ J) [IsLocalHom v.toRingHom]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map v.toRingHom)) :
    ∃ w : S →ₐ[R] A, (Ideal.Quotient.mkₐ R J).comp w = v := by
  sorry

end Algebra
