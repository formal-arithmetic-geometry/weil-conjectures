/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.EtaleFieldPointFunctor
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Sheaf.AlgebraicGeometry.EtaleComponents

/-!
# Connected and reduced factors of a finite commutative group scheme

Source: Milne, Algebraic Groups (2017), Proposition 11.3, printed p. 210, and
Proposition 2.37, printed pp. 51-52
(blueprint: lem-sfb-perfect-finite-commutative-reduced-splitting).

The identity component has its open subscheme structure, including nilpotents.
The reduced factor is the actual nilradical subscheme. The splitting map is
multiplication of their canonical inclusions, over the original field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Over a perfect field of positive characteristic, the identity component and
reduction of a finite commutative group scheme are closed subgroups, the reduction
is finite etale, and multiplication is an isomorphism of group schemes.
Source: Milne, Algebraic Groups (2017), Proposition 11.3, printed p. 210, with
Proposition 2.37, printed pp. 51-52
(blueprint: lem-sfb-perfect-finite-commutative-reduced-splitting).

Proof:
1. Write G = Spec B and C = B / sqrt(0). The reduced-induced-closed-subscheme
   theorem (lem-weil-pbc-reduced-induced-closed-subscheme) makes Spec C reduced.
   It is finite over k. By lem-a1-finite-reduced-perfect-algebra-etale and
   lem-weil-pbc-etale-ring-map-iff-etale-affine it is etale. The tensor product
   C tensor C is reduced by lem-weil-pbc-perfect-reduced-tensor; the affine
   fibre-product description (lem-weil-pbc-fibre-product-affine-spectra) thus
   lets multiplication, inversion and the identity factor uniquely through
   the reduction. The group axioms descend through its closed immersion.
2. Apply lem-sfb-algebraic-scheme-etale-components to the finite, hence affine
   and separated G. Preservation of products and the terminal object gives
   its component scheme P a commutative group structure and makes q : G -> P
   a homomorphism. The identity of the finite etale P is a clopen copy of
   Spec k. Its inverse image H is therefore a clopen kernel subgroup with
   precisely the open subscheme structure of the connected identity component.
3. A separable closure K of k (def-pd-separable-closure) is perfect: if a is
   separable over k, its purely inseparable extension over k(a^p) is trivial;
   expressing a in k[a^p] and taking p-th roots of its coefficients gives a
   p-th root in K. Thus K is algebraically closed. By the component theorem
   and lem-weil-pbc-finite-type-dim-zero-artinian, G_K has one K-point per
   component, so G(K) -> P(K) is bijective. Killing nilpotents gives
   G_red(K) = G(K). Both G_red and P are etale, so
   lem-exc-etale-field-point-functor-fully-faithful lifts the inverse equivariant
   bijection to an inverse v of u : G_red -> P over k.
4. Set r = v q and a(x) = x j(r(x))^(-1), where j is the reduction inclusion.
   Then q(a(x)) is the identity, so a factors through H. On every test scheme,
   multiplication H x G_red -> G and (a,r) are inverse: a(x) j(r(x)) = x,
   r(h j(z)) = z and a(h j(z)) = h. Commutativity makes multiplication a
   homomorphism, hence gives the asserted isomorphism of group schemes. -/
theorem GrpObj.perfect_finite_commutative_reduced_splitting
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hperfect : ∀ a : k, ∃ b : k, b ^ p = a)
    (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G] [IsFinite G.hom] :
    IsClosedSubgroupScheme (GrpObj.identityComponentι G) ∧
      ∃ (_ : GrpObj (Over.mk (G.left.nilradical.subschemeι ≫ G.hom))),
        IsClosedSubgroupScheme
          (Over.homMk G.left.nilradical.subschemeι :
            Over.mk (G.left.nilradical.subschemeι ≫ G.hom) ⟶ G) ∧
        IsFinite (G.left.nilradical.subschemeι ≫ G.hom) ∧
        Etale (G.left.nilradical.subschemeι ≫ G.hom) ∧
        IsMonHom ((GrpObj.identityComponentι G ⊗ₘ
          (Over.homMk G.left.nilradical.subschemeι :
            Over.mk (G.left.nilradical.subschemeι ≫ G.hom) ⟶ G)) ≫ μ[G]) ∧
        IsIso ((GrpObj.identityComponentι G ⊗ₘ
          (Over.homMk G.left.nilradical.subschemeι :
            Over.mk (G.left.nilradical.subschemeι ≫ G.hom) ⟶ G)) ≫ μ[G]) := by
  sorry

end AlgebraicGeometry
