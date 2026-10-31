/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup
public import WeilConjectures.AlgebraicGeometry.DiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.AlgebraicGeometry.LinearGroupSchemes
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A central diagonalizable subgroup meets the derived group in a finite scheme

Source: Milne, Algebraic Groups (2017), Proposition 12.46(a), pp.245--246,
with Theorem 12.12 and Remark 12.13, pp.234--235, for diagonalizable weight spaces.
(blueprint: lem-sfb-central-diagonalizable-derived-intersection-finite).

The intersection is a pullback over the ambient group, retaining its scheme structure.
In particular, diagonalizable subgroups with characteristic torsion are allowed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- A central diagonalizable closed subgroup of a smooth connected affine finite-type
group has finite scheme-theoretic intersection with its derived group.
Source: Milne, Proposition 12.46(a), pp.245--246, extended using Theorem 12.12 and
Remark 12.13, pp.234--235.
(blueprint: lem-sfb-central-diagonalizable-derived-intersection-finite).

Proof:
1. Apply lem-sfb-central-torus-faithful-weight-blocks with the trivial central torus
   to obtain a closed faithful representation of G on a nonzero finite-dimensional V.
2. By lem-sfb-diagonalizable-representation-weight-grading, restriction to C decomposes
   V into finitely many nonzero weight spaces V_i. Centrality over every algebra implies
   that G preserves these summands, giving representations rho_i on V_i. On C their
   matrices are chi_i times the identity, where chi_i is the corresponding character.
3. By def-sc-general-linear-group, det composed with rho_i is a character of G.
   By lem-sfb-smooth-connected-derived-subgroup it is trivial on the derived group.
   Hence on K = C ×_G D the functions a_i = chi_i restricted to K satisfy
   a_i^(dim V_i) = 1, as identities of functions over all test algebras.
4. By def-sc-group-scheme-subgroup and def-weil-closed-immersion, K is the closed
   subscheme cut out by the sum of the two subgroup ideals. The faithful representation
   gives a surjection from the GL coordinate algebra to F[K]. In the weight basis,
   its matrix coordinates restrict to zero or a_i and its inverse determinant to one.
   Thus F[K] is a quotient of F[t_i]/(t_i^(dim V_i)-1). Monomials with each exponent
   smaller than the corresponding positive dim V_i span this algebra, proving finite
   dimensionality and therefore finiteness over F. No reducedness or division by the
   block dimensions is used. -/
theorem central_diagonalizable_derived_intersection_finite
    {F : Type u} [Field F] [IsAlgClosed F]
    (G C D : Grp (Over (Spec (.of F))))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (i : C ⟶ G) (hi : IsClosedSubgroupScheme i.hom.hom)
    (hcentral : ∀ (R : Type u) [CommRing R] [Algebra F R]
      (c : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F R))) ⟶ C.X)
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F R))) ⟶ G.X),
      Commute (c ≫ i.hom.hom) g)
    (hdiag : ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (C ≅ diagonalizableGroup F M))
    (j : D ⟶ G) (hderived : IsDerivedGroupScheme j.hom.hom) :
    IsFinite (pullback i.hom.hom j.hom.hom).hom := by
  sorry

end AlgebraicGeometry
