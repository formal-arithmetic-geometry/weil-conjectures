/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Sheaf.AlgebraicGeometry.IrreducibleProductOverField
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Sheaf.AlgebraicGeometry.SchemeProductDimension
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# A connected smooth almost-complement to a central abelian subvariety

Source: Milne, Algebraic Groups (2017), Theorem 8.24, printed p.153;
Proposition 5.23, printed p.104; Proposition 1.34 and Corollary 1.35.
(blueprint: lem-sfb-rosenlicht-connected-almost-complement)

The cartesian tensor product in `Over (Spec k)` is the scheme-theoretic fibre product.
The product of morphisms to a group object is their pointwise multiplication, so the
specified map `m` sends `(a,n)` to `i(a) * j(n)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A central abelian subvariety has a smooth connected closed normal almost-complement.

Source: Milne, Algebraic Groups (2017), Theorem 8.24, printed p.153, with the
connected refinement using Proposition 1.34 and Corollary 1.35; Proposition 5.23,
printed p.104, gives the dimension formula.
(blueprint: lem-sfb-rosenlicht-connected-almost-complement)

Proof plan, following the ten steps of the DAG node:
1. Apply lem-sfb-abelian-subgroup-equivariant-multiple-map to obtain n > 0 and
   phi : G → A. Translate by phi(e) to get r(e) = 0 and r restricted to A equal to [n].
   By lem-sfb-locally-algebraic-group-identity-component and
   sbc-lem-smooth-geometrically-reduced, G is geometrically integral.
   Apply lem-sfb-abelian-product-axis-rigidity to r(xy)-r(x)-r(y), which vanishes
   on both identity axes. This proves homomorphy; lem-sc-av-commutative justifies
   taking these differences in A.
2. By lem-sfb-algebraic-group-homomorphism-factorization, K = ker(r) is closed,
   normal and finite type. Put N = (K^0)_red. The identity-component theorem makes
   N smooth, connected, separated and finite type. Its inclusion is closed by
   lem-weil-pbc-closed-immersion-products, composing the reduction and component inclusions.
3. Conjugation G × N → K has connected image containing e, by
   lem-sc-irreducible-product-over-field, so factors through K^0 using
   lem-weil-pbc-morphism-factors-through-open-subscheme. The source is reduced by
   lem-weil-pbc-perfect-reduced-tensor. Apply
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme to factor through N.
   On all algebra-valued points this is precisely normality.
4. Centrality of A makes (a,n) ↦ an a homomorphism. The product is separated and
   finite type by the closed-diagonal product clause of
   lem-weil-pbc-closed-immersion-products and finite-type affine tensor products.
5. The intersection A ×_G N embeds into A[n]. By lem-sc-mult-n-isogeny,
   lem-weil-pbc-closed-immersion-finite and lem-weil-pbc-finite-composition it is finite.
   The map a ↦ (a,i(a)^(-1)) identifies this intersection with ker(m), on every
   test algebra and hence as schemes. No reducedness of the kernel is asserted.
6. Apply lem-sfb-algebraic-group-homomorphism-factorization to m, obtaining its
   closed image I and a faithfully flat finitely presented map to I.
7. By lem-sfb-group-neutral-component-translates, K has finitely many translates
   of K^0, represented by k-points k_i. Reduced-source factorization identifies
   K^0(k) with N(k). By lem-sc-isogeny-surjective, [n] is surjective on A(k).
   Thus every g in G(k) belongs to one of the finitely many translates k_i I(k).
8. By lem-sc-translation-automorphism the translates are closed. By
   lem-weil-pbc-closed-point-residue-field-base and lem-sc-lft-over-field-jacobson-space,
   they cover G. Irreducibility forces one translate to equal G. Translating back
   gives |I| = |G|; reduced-source factorization makes the closed immersion I → G
   an isomorphism. Hence m is faithfully flat and finitely presented.
9. The finite kernel has the identity point, so lem-sc-finite-surjective-dimension
   gives its dimension as dim(Spec k) = 0.
10. By the factorization theorem and lem-weil-pbc-fpqc-representable-descent, G is
    also the fpqc quotient of A × N by ker(m): local lifts exist and two lifts differ
    by a kernel point. Apply lem-sfb-homogeneous-quotient-krull-dimension and then
    lem-sfb-scheme-product-dimension to get dim G = dim A + dim N. -/
theorem rosenlicht_connected_almostComplement
    {k : Type u} [Field k] [IsAlgClosed k]
    (G A : Over (Spec (.of k))) [GrpObj G] [GrpObj A]
    [Smooth G.hom] [ConnectedSpace G.left] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsAbelianVariety A]
    (i : A ⟶ G) [IsClosedSubgroupScheme i]
    (hcentral : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ A)
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G),
      Commute (a ≫ i) g) :
    ∃ (N : Over (Spec (.of k))) (_ : GrpObj N) (j : N ⟶ G) (m : A ⊗ N ⟶ G),
      Smooth N.hom ∧ ConnectedSpace N.left ∧ IsSeparated N.hom ∧
      LocallyOfFiniteType N.hom ∧ QuasiCompact N.hom ∧
      IsClosedSubgroupScheme j ∧ IsNormalSubgroupScheme j ∧
      m = (fst A N ≫ i) * (snd A N ≫ j) ∧ IsMonHom m ∧
      Flat m.left ∧ Surjective m.left ∧ LocallyOfFinitePresentation m.left ∧
      QuasiCompact m.left ∧ QuasiSeparated m.left ∧ IsFinite (GrpObj.ker m).hom ∧
      topologicalKrullDim G.left = topologicalKrullDim A.left + topologicalKrullDim N.left := by
  sorry

end AlgebraicGeometry
