/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import WeilConjectures.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.AlgebraicGeometry.ProperReducedGlobalSectionsProduct
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.ZeroDimIntegralPoint
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Precoverage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Proper subschemes of solvable homogeneous spaces

Source: Milne, Algebraic Groups (2017), Theorem 17.1, printed p.352;
Propositions 5.24--5.25 and 7.11, printed pp.104--105 and 141--142.
(blueprint: lem-sfb-solvable-homogeneous-proper-subschemes)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A solvable homogeneous space has no positive-dimensional proper closed subscheme.
If the entire quotient is proper, the specified closed subgroup inclusion is an
isomorphism, expressing equality with the ambient group as a closed subgroup scheme.
The isomorphism `e`, with its two projection identities, is exactly the map
`(g,b) ↦ (g,gb)`, rather than an unspecified isomorphism of its source and target.

Source: Milne, Algebraic Groups (2017), Theorem 17.1, printed p.352;
Propositions 5.24--5.25 and 7.11, printed pp.104--105 and 141--142.
(blueprint: lem-sfb-solvable-homogeneous-proper-subschemes)

Proof, following the eleven steps of the node:
1. Compare Q with G/K by fpqc descent along the two quotient maps, using their
   common kernel pair G × K and right invariance. Finite-type cancellation gives
   quasi-compactness. Uniqueness of descent makes the comparisons inverse. Descend
   left multiplication too; the stabilizer at the identity coset is exactly K.
   Use lem-sfb-homogeneous-orbit-quotient-geometry,
   lemma-nagata-finite-type-to-separated-target,
   lem-weil-pbc-fpqc-representable-descent and lem-galois-fpqc-covering-base-change.
2. The orbit-quotient and smooth-orbit lemmas make Q smooth and reduced. The identity
   component lemma makes G irreducible, so Q is integral. Induct strongly on dim G,
   simultaneously for all closed subgroups. The dimension bound is supplied by
   lem-sfb-solvable-normal-subgroup-products. At dimension zero, the integral-point
   lemma makes G = Spec k; its identity forces its only closed subgroup to be G.
3. Replace K by H = (K⁰)red. The nested-quotient lemma gives a finite faithfully flat
   G/H → G/K. Pull Z back to a nonempty proper closed W in G/H. Closed-immersion
   base change, finite-morphism permanence, surjective base change and finite
   surjective dimension invariance give dim W = dim Z.
4. Reduce W, using lem-weil-pbc-reduction-universal-homeomorphism and closed-immersion
   properness. The proper reduced global-sections product lemma splits it into
   finitely many clopen connected components C with Γ(C) = k. Every chain of
   irreducible closed subsets lies in a single component, so treat each C.
5. Let D be the derived subgroup. The smooth connected derived-subgroup lemma and
   solvable-normal-subgroup-products lemma give a smooth connected normal affine
   finite-type D with dim D < dim G. Containment of successive commutators shows
   that smooth connected subgroups inherit solvability. D = G would contradict
   termination of the derived series unless G were trivial.
6. Form A = G/D by lem-sfb-affine-normal-quotient-geometry. Factor H → A through
   its faithfully flat image I by the algebraic-group-homomorphism-factorization
   lemma; its kernel is D ∩ H, so I = H/(D ∩ H) is smooth connected. The inverse
   image N = G ×[A] I is smooth connected affine finite type and contains D and H.
7. Lift sections locally through H → I to see N = DH as fppf sheaves. The quotient
   A is commutative because commutators lie in D, so I is normal and N is normal
   in G. N is solvable by step 5. If N ≠ G, its dimension is strictly smaller.
8. If N = G, identify D/(D ∩ H) with G/H: local surjectivity is G = DH, and equal
   cosets differ by D ∩ H. Glue the local inverse by fpqc representable descent.
   Apply induction to D and its arbitrary closed subgroup D ∩ H.
9. Otherwise form the affine B = G/N. The nested-quotient lemma gives G/H → B.
   The morphism-into-affine-scheme lemma and Γ(C) = k make C map to a k-point y.
   Lift y to g ∈ G(k) by the homogeneous-quotient rational-lift clause. The nested
   quotient translated-fibre clause identifies the fibre with N/H. The induced
   C → N/H is a closed immersion by base change.
10. Apply induction to the smaller smooth connected solvable N to obtain dim C = 0.
    Steps 4 and 3 give dim Z = 0. This includes D = 1, H = 1 and H = G; the
    intersections in step 8 need not be smooth or connected.
11. If Q is proper, take Z = Q. Q is nonempty and integral, so dimension zero and
    lem-weil-pbc-zero-dim-integral-point identify Q with Spec k. Pull the specified
    kernel-pair isomorphism back along the identity of G in its first coordinate.
    The given K → G is the fibre over q(e), which is now all of G. This retains
    the infinitesimal scheme structure and proves that the inclusion is an isomorphism.
-/
theorem solvable_homogeneous_proper_subschemes
    {k : Type u} [Field k] [IsAlgClosed k]
    (G K : Over (Spec (.of k))) [GrpObj G] [GrpObj K]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hsolv : IsSolvableGroupScheme G)
    (i : K ⟶ G) [IsClosedSubgroupScheme i]
    (Q : Over (Spec (.of k)))
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (q : G ⟶ Q) [Flat q.left] [Surjective q.left]
    (hinv : fst G K ≫ q = lift (fst G K) (snd G K ≫ i) ≫ μ[G] ≫ q)
    (e : G ⊗ K ≅ pullback q q)
    (he₁ : e.hom ≫ pullback.fst q q = fst G K)
    (he₂ : e.hom ≫ pullback.snd q q = lift (fst G K) (snd G K ≫ i) ≫ μ[G]) :
    (∀ (Z : Over (Spec (.of k))) (j : Z ⟶ Q),
      IsClosedImmersion j.left → Nonempty Z.left → IsProper Z.hom →
        topologicalKrullDim Z.left = 0) ∧
    (IsProper Q.hom → IsIso i) := by
  sorry

end AlgebraicGeometry
