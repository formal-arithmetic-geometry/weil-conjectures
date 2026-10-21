/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover

/-!
# The invariant ring of inertia is etale at the contracted prime

Source: Stacks Project, Tag 0BST, `lemma-inertia-invariants-etale` in `pione.tex`.
(blueprint: lem-dl-a1-finite-group-inertia-invariants-etale)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- The inclusion of full invariants into inertia invariants is etale on an open
neighbourhood of the contracted prime. The inertia subgroup `q.asIdeal.inertia G`
consists of the `g` with `g • r - r ∈ q.asIdeal` for every `r`. This is exactly
preservation of the prime and the identity action on `Frac(R / q)`: identity on the
quotient extends to its fraction field, and conversely the quotient embeds in that field.
No Noetherian, module-finiteness, faithful-action, or group-order-invertibility
hypothesis is imposed.

Source: Stacks Project, Tag 0BST, `lemma-inertia-invariants-etale`.
(blueprint: lem-dl-a1-finite-group-inertia-invariants-etale)

Proof:
1. Put A = R^G and C = R^I. By lem-dl-a1-finite-invariant-prime-orbits-residues,
   R is integral over A, the primes above the contracted prime form a finite G-orbit,
   and their residue extensions are algebraic normal with finite automorphism groups.
   Apply lem-dl-a1-integral-normal-residue-etale-splitting to obtain an etale A-algebra B,
   a prime p' of B, and a lift q' of q in S = B tensor_A R. It gives a finite product
   decomposition of S with one prime over p' in each factor and purely inseparable
   residue extensions. Label the factor containing q' by 1.
2. Inertia is unchanged by this base change: if g • r - r lies in q for every r,
   the same holds at q' for sums of pure tensors; conversely apply the condition to
   1 tensor r and contract to q. This is the elementary difference criterion for inertia,
   using def-weil-pbc-module-tensor-product; it also works after base localization.
3. B is flat over A by def-weil-etale-morphism. Apply
   lem-dl-a1-flat-base-change-finite-invariants with G and I to identify S^G = B and
   S^I = B tensor_A C. Thus Spec(S^I) is the base change of Spec C over Spec A,
   and Spec(S^I) -> Spec C is etale by lem-weil-pbc-etale-scheme-base-change.
4. Refine the clopen partition of Spec S by all its G-translates. Its nonempty atoms
   are permuted by G and each contains at most one fibre point. The union of atoms
   containing no fibre point is closed. Its image is closed by integrality and
   lem-weil-pbc-integral-spec-closed-map and misses p'. Localize B away from p' to
   remove this image; this preserves etaleness by
   lem-weil-pbc-etale-composition-cancellation. The atoms now each contain one fibre point.
   By lem-weil-pbc-spec-clopen-idempotent they yield orthogonal idempotents summing to 1
   and a G-permuted product S = product_j e_j S. Localization has not changed the residues.
5. The stabilizer of q' acts trivially on its purely inseparable residue extension,
   hence is I. It is also the stabilizer of the first factor. Transitivity on fibre
   primes, by lem-dl-a1-finite-invariant-prime-orbits-residues, gives transitivity on
   factors. Projection identifies S^G with (e_1 S)^I: choose coset representatives g_j
   sending factor 1 to factor j and send a to the tuple (g_j(a)). The identity
   g g_j = g_k h with h in I proves invariance and independence of representatives.
   Projection and this tuple construction are inverse. Thus B = (e_1 S)^I.
6. Since I fixes e_1, S^I = (e_1 S)^I times ((1-e_1)S)^I. Its first spectrum component
   W contains the contracted q' and is isomorphic over B to Spec B. Its inclusion is
   open by lem-weil-pbc-finite-affine-coproduct-spectrum. The map W -> Spec C is etale
   by step 3 and lem-weil-pbc-etale-composition-cancellation, so its image U is open by
   lem-weil-pbc-etale-morphism-open-map and contains the contracted q. The map W -> U is
   surjective etale, and W -> Spec A is etale. Apply
   lem-trf-etale-descent-through-source-cover to conclude that U -> Spec A is etale. -/
theorem exists_etale_neighborhood_inertia_invariants
    (G : Type v) [Group G] [Finite G] (R : Type u) [CommRing R]
    [MulSemiringAction G R] (q : PrimeSpectrum R) :
    ∃ U : (Spec (.of (FixedPoints.subring R (q.asIdeal.inertia G)))).Opens,
      PrimeSpectrum.comap (FixedPoints.subring R (q.asIdeal.inertia G)).subtype q ∈ U ∧
      Etale (U.ι ≫ Spec.map (CommRingCat.ofHom
        (Subring.inclusion (fun (x : R) (hx : x ∈ FixedPoints.subring R G)
          (g : q.asIdeal.inertia G) ↦ hx g.1) :
          FixedPoints.subring R G →+* FixedPoints.subring R (q.asIdeal.inertia G)))) := by
  sorry

end AlgebraicGeometry
