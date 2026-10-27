/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Universally closed morphisms of algebraic spaces are quasi-compact

Source: Stacks Project, Morphisms of Spaces, Tag 04XW,
lemma-universally-closed-quasi-compact
(blueprint: lem-sfb-space-universally-closed-quasicompact).

The hypothesis tests closedness after every algebraic-space base change. The conclusion
uses the existing affine-scheme test definition with the atlas topology on point classes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A universally closed morphism of algebraic spaces is quasi-compact, with no
representability, separatedness, finite-type or Noetherian assumption.
Source: Stacks Project, Morphisms of Spaces, Tag 04XW,
lemma-universally-closed-quasi-compact
(blueprint: lem-sfb-space-universally-closed-quasicompact).

Proof:
1. Fix an affine scheme mapping to the target and base change the morphism to it.
   Sheaf fibre-product associativity (lem-trf-space-fibre-products-etale-covers) preserves
   universal closedness as defined in def-sfb-space-morphism-properties. Thus it suffices
   to prove compactness of the source point space when the target is Spec B.
2. Suppose that source is not quasi-compact. Choose a cover by quasi-compact open
   subspaces Xi using lem-a1-space-affine-atlas-open-cover and lem-a1-space-etale-open-image.
   Since Spec B is quasi-separated (lem-weil-pbc-affine-scheme-qcqs), each Xi maps
   quasi-compactly to it (lem-sfb-space-qcqs-permanence). Every principal-open restriction
   of Xi is therefore quasi-compact, by lem-a1-space-point-open-calculus.
3. Some point y of Spec B has no principal-open neighbourhood with quasi-compact inverse
   image: otherwise finitely many such neighbourhoods cover Spec B and their inverse
   images make the source quasi-compact. Use lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact
   and lem-weil-pbc-spec-localization-away-basic-open for this finite-cover argument.
4. Set A = B[a_i], T = Spec A, and Ti = D(a_i), using def-weil-pbc-mv-polynomial-ring
   and def-weil-affine-spectrum. In P = T times over Spec B the source, remove the union
   of the intersections p inverse Ti with q inverse Xi. Point-map continuity makes the
   complement C closed (lem-a1-space-point-open-calculus). Universal closedness makes
   its image F under p closed in T.
5. Let t over y evaluate all a_i to 1 in the residue field. The covering by Xi implies
   t is not in F. Choose a principal open D(g) containing t and disjoint from F, using
   lem-weil-pbc-prime-residue-field-algebra and lem-weil-pbc-spec-localization-away-basic-open.
6. Only finitely many variables, indexed by J, occur in g. One coefficient c survives
   at y. Over V = D(c), choose x outside all Xj for j in J: those finitely many
   quasi-compact opens cannot cover the non-quasi-compact inverse image of V.
   Write v for the image of x, using lem-a1-space-point-open-calculus.
7. In the domain kappa(v)[u_j : j in J], g remains nonzero because c survives at v.
   Pass to the residue field of its zero prime and send all other variables to zero.
   This gives t' over v with g(t') nonzero and a_i(t') zero for i outside J.
   Use lem-weil-pbc-polynomial-ring-domain, lem-weil-pbc-prime-residue-field-algebra,
   def-weil-pbc-mv-polynomial-ring and def-weil-affine-spectrum. This also covers empty J
   and finite residue fields.
8. Lift the compatible points x and t' to a point z of P, by the point fibre-product
   surjectivity in lem-a1-space-point-open-calculus. For j in J its q-image avoids Xj;
   for i outside J its p-image avoids Ti. Hence z belongs to C, so t' belongs to F,
   contradicting F contained in V(g). The contradiction proves compactness on each
   affine test, exactly MapIsQuasiCompact. -/
theorem mapIsQuasiCompact_of_mapIsUniversallyClosed {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : MapIsUniversallyClosed f) :
    MapIsQuasiCompact f.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
