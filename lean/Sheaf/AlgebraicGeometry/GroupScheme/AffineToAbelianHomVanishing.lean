/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.RingTheory.Artinian.Ring

/-!
# Homomorphisms from affine groups to abelian varieties

Source: Milne, Algebraic Groups (2017), Proposition 8.1(b) and Example 8.4, p.149,
and Theorem 5.39, pp.108--109
(blueprint: lem-sfb-affine-to-abelian-hom-vanishing).

The affine source need not be commutative. The conclusion is equality of scheme
morphisms with the structure morphism followed by the target's identity section.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- Every homomorphism from a smooth connected affine finite-type group scheme over
an algebraically closed field to an abelian variety is the zero homomorphism.

Source: Milne, Algebraic Groups (2017), Proposition 8.1(b) and Example 8.4, p.149,
and Theorem 5.39, pp.108--109
(blueprint: lem-sfb-affine-to-abelian-hom-vanishing).

Proof:
1. The abelian variety is proper, hence separated and finite type; the source is
   separated by lem-sc-group-scheme-separated-field. Apply
   lem-sfb-algebraic-group-homomorphism-factorization to write f = q followed by i,
   with q faithfully flat and finitely presented, i a closed immersion, and I the
   fppf quotient of L by its closed normal scheme-theoretic kernel N.
2. The closed subgroup N of affine L is affine. Apply
   lem-sfb-affine-normal-quotient-geometry to obtain an affine quotient Q, smooth
   and connected because L is so and k is algebraically closed. No smoothness
   of N is needed.
3. Both I and Q represent the fppf sheafification of the same coset presheaf.
   Its universal property gives inverse natural maps on affine tests. Extend
   them to all schemes by affine-open gluing, using
   lem-weil-pbc-fpqc-representable-descent, then apply
   lem-galois-yoneda-fully-faithful. Thus I is affine, smooth and connected.
4. By lem-weil-pbc-closed-immersion-proper, I is proper. Apply
   lem-sc-proper-affine-finite-general: I = Spec B with B finite-dimensional over k.
5. By sbc-lem-smooth-geometrically-reduced, B is reduced. Its identity section
   makes B nonzero. Connectedness and lem-pc-scheme-connected-iff-idempotents
   show that its only idempotents are 0 and 1. Apply
   lem-pc-alg-closed-reduced-algebra-no-idempotents-dim-one: k → B is an
   isomorphism, inverse to the identity section's map. Hence p_I and e_I are inverse.
6. Since i preserves identity, i composed with e_I is e_A. Substituting
   id_I = e_I composed with p_I into f = i composed with q gives
   f = e_A composed with p_L as scheme morphisms, including on nonreduced tests.
   This calculation also covers L = 1 and A = 1. -/
theorem affine_to_abelian_hom_vanishing {k : Type u} [Field k] [IsAlgClosed k]
    (L A : Grp (Over (Spec (.of k)))) [Smooth L.X.hom] [ConnectedSpace L.X.left]
    [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom] [QuasiCompact L.X.hom]
    [IsAbelianVariety A.X] (f : L ⟶ A) :
    f.hom.hom.left = L.X.hom ≫ (η[A.X]).left := by
  sorry

end AlgebraicGeometry
