/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Connected.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.RingTheory.Artinian.Ring
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # A connected affine group without tori is unipotent

Source: Milne, Algebraic Groups (2017), Proposition 16.60, printed p.346;
Theorem 4.9 and Corollary 4.10, printed p.87; Corollaries 14.6 and 14.12,
printed pp.282--283 (blueprint: lem-sfb-no-torus-unipotent).

Triviality of every torus subgroup is expressed by triviality of every closed
homomorphism from a finite product of the recorded multiplicative group. Rank zero
is included. The conclusion retains the closed immersion and the positive exponent
for each rational point, rather than merely an abstract-group nilpotence property.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth connected affine finite-type group with no nontrivial torus has a
closed faithful representation all of whose k-points are unipotent matrices.
Source: Milne, Proposition 16.60, p.346; Theorem 4.9 and Corollary 4.10, p.87;
Corollaries 14.6 and 14.12, pp.282--283 (blueprint: lem-sfb-no-torus-unipotent).

Proof:
1. Apply lem-sfb-solvable-subgroup-flag-realization to the trivial subgroup to get
   a nonzero faithful finite-dimensional representation and its projective complete
   flag scheme. Choose an orbit of least dimension. The boundary clause of
   lem-sfb-smooth-group-orbit-geometry makes it closed, hence proper. For a point x,
   lem-sfb-homogeneous-orbit-quotient-geometry identifies this orbit O with G/J,
   where J is the possibly nonsmooth stabilizer.
2. Put K = (J^0)_red. The flag-realization lemma makes K smooth, connected and
   solvable. By lem-sfb-nested-homogeneous-quotient-geometry the map G/K to G/J
   is finite faithfully flat. By lem-sfb-affine-proper-finite and
   lem-weil-pbc-proper-composition, Q = G/K is proper.
3. The field is perfect. Apply lem-sfb-perfect-solvable-unipotent-torus to K to
   get its normal unipotent subgroup K_u and torus quotient D. The solvable series
   gives the required commutative quotients. K is its own Borel, so
   lem-sfb-borel-maximal-torus-conjugacy supplies a maximal torus T of K. Its
   inclusion in G is trivial by hypothesis. By lem-sfb-solvable-torus-complements,
   T maps isomorphically to D, so D is trivial. The kernel clause of
   lem-sfb-affine-normal-quotient-geometry gives K = K_u, hence K is unipotent.
4. By lem-sfb-geometric-unipotence-unitriangular-embedding, K has a closed
   unitriangular embedding, faithful on every algebra of points. Apply
   lem-sfb-unipotent-homogeneous-quasiaffine to obtain an immersion Q into affine
   space. This is a monomorphism since open and closed immersions are monomorphisms.
5. By lem-sfb-homogeneous-orbit-quotient-geometry the quotient map G to Q is flat
   and surjective, and Q is separated of finite type. By
   lem-sfb-nested-homogeneous-quotient-geometry it is finitely presented. Apply
   lem-sbc-smooth-flat-surjective-source-descent to obtain smoothness of Q; then
   sbc-lem-smooth-geometrically-reduced makes Q reduced. It is nonempty because
   it contains the image of the identity and connected by surjectivity from G.
6. By lem-weil-pbc-proper-to-separated the immersion into affine space is proper.
   By lem-pc-proper-monomorphism-closed it is a closed immersion, so Q is affine
   by lem-weil-pbc-closed-immersion-integral-separated-uc. Its proper structure
   map is finite by lem-sfb-affine-proper-finite.
7. Write Q = Spec B. By def-weil-finite-integral-morphism, B is finite-dimensional
   over k. Reducedness means no nonzero nilpotents, nonemptiness means 1 is not 0,
   and connectedness with lem-pc-scheme-connected-iff-idempotents means the only
   idempotents are 0 and 1. Apply
   lem-pc-alg-closed-reduced-algebra-no-idempotents-dim-one: k to B is an
   isomorphism. Thus Q is Spec k as a scheme.
8. Pull back the quotient torsor identity of
   lem-sfb-homogeneous-orbit-quotient-geometry along the identity point. It
   identifies K with the fibre of G to Q. Since Q is Spec k, K is all of G.
   By step 3 G is unipotent. Apply
   lem-sfb-geometric-unipotence-unitriangular-embedding to get a closed immersion
   into GL_m factoring through the unitriangular matrices, with m positive.
   For each g, the matrix A = rho(g) - I is strictly upper triangular. Every term
   in an entry of A^m requires a strictly increasing chain of m+1 indices among
   m indices, so A^m = 0. Take rho to be this immersion and N = m. -/
theorem exists_unipotent_representation_of_no_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hNoTorus : ∀ (r : ℕ) (i : (MultiplicativeType.splitTorus k r).X ⟶ G),
      IsClosedSubgroupScheme i → i = 1) :
    ∃ (m : ℕ), 1 ≤ m ∧
      ∃ rho : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) k,
        IsMonHom rho ∧ IsClosedImmersion rho.left ∧
        ∀ g : (Spec (.of k)).asOver (Spec (.of k)) ⟶ G,
          ∃ N : ℕ, 1 ≤ N ∧
            ((GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} m) k k
              (g ≫ rho)).val - 1) ^ N = 0 := by
  sorry

end AlgebraicGeometry
