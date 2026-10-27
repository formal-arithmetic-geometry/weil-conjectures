/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NP
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.GaloisDescentAffineSubgroups
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsSepClosed

/-! # Separable base change of the solvable radical

Source: Milne, Algebraic Groups (2017), Proposition 19.1, printed p.397,
with 6.19(a), 6.31 and 6.44, printed pp.129,132,135.
(blueprint: lem-sfb-solvable-radical-separable-base-change)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The largest smooth connected solvable normal closed subgroup is preserved by every
separable algebraic field extension, including infinite extensions. Solvability is
termination of the scheme-theoretic derived series, not solvability of rational points.
Source: Milne, Proposition 19.1, printed p.397, with 6.19(a), 6.31 and 6.44.
(blueprint: lem-sfb-solvable-radical-separable-base-change).

Proof:
1. Reconcile the derived-series and closed subnormal-series definitions of solvability.
   By lem-sfb-derived-commutator-word-arbitrary-field, the successive derived subgroups
   of a smooth connected affine group are smooth and geometrically connected and commute
   with arbitrary field extension. Each successive quotient is commutative. Conversely,
   lem-sfb-affine-normal-quotient-geometry represents the commutative successive quotients
   of a solvable series, so the universal property of the derived subgroup inductively
   places the derived series inside that series. Inclusion and equality detection in
   lem-sfb-galois-descent-affine-subgroups then show that solvability is preserved and
   reflected by every field extension for these smooth connected groups.
2. Over any field, choose a smooth connected solvable normal closed subgroup of greatest
   dimension. The identity subgroup provides a candidate. By
   lem-sfb-solvable-normal-subgroup-products, dimensions are nonnegative integers bounded
   by the ambient dimension. Its product with any other candidate is another candidate;
   strict dimension growth forces that product to equal the chosen subgroup. Thus the
   chosen subgroup contains every candidate and is unique. Over k it is R.
3. For a possibly infinite Galois extension L/k, let U be this largest subgroup of G_L.
   Every Galois automorphism carries U to another largest subgroup, hence preserves U
   as a closed subgroup scheme. Its ideal is therefore semilinearly stable. Apply
   lem-sfb-galois-descent-affine-subgroups to descend U to a normal closed subgroup N.
4. N is affine of finite type. By
   lem-weil-pbc-field-extension-base-change-faithfully-flat and
   lem-weil-pbc-faithfully-flat-surjective-spectrum, N_L to N is a continuous surjection
   and the extension of bases is faithfully flat. Spec L to Spec k is quasi-compact.
   Apply lem-trf-smooth-fpqc-base-descent to descend smoothness. Connectedness descends
   along the continuous surjection, and step 1 reflects solvability. Maximality gives
   N contained in R.
5. The product node preserves smoothness, connectedness and solvability of R_L; the
   subgroup-descent node preserves normality. Maximality of U gives R_L contained in U,
   hence R contained in N by inclusion detection. Thus N equals R and U equals R_L.
6. Embed the given separable algebraic K/k into a separable closure Omega of k using
   lem-weil-pbc-separable-closure-exists-galois and
   lem-weil-pbc-separable-extension-embeds-separably-closed. Omega/k is Galois, so step 5
   applies. For any smooth connected solvable normal closed V in G_K, its base change
   to Omega has the same properties and is contained in R_Omega. Inclusion detection
   for Omega/K gives V contained in R_K. No finiteness or normality of K/k is needed.
7. R_K itself is smooth, connected and solvable by the product node and step 1, normal
   by the subgroup-descent node, and closed by base change of its defining ideal.
   Together with step 6 this proves every asserted clause. -/
theorem solvable_radical_separable_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (G R : Over (Spec (.of k))) [GrpObj G] [GrpObj R]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [GeometricallyConnected G.hom]
    (i : R ⟶ G) [IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i]
    [Smooth R.hom] [ConnectedSpace R.left] (hR : IsSolvableGroupScheme R)
    (hmax : ∀ (N : Over (Spec (.of k))) [GrpObj N] (j : N ⟶ G),
      IsClosedSubgroupScheme j → IsNormalSubgroupScheme j →
      Smooth N.hom → ConnectedSpace N.left → IsSolvableGroupScheme N →
      ∃ f : N ⟶ R, f ≫ i = j) :
    IsClosedSubgroupScheme
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) ∧
    Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj R).hom ∧
    ConnectedSpace
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj R).left ∧
    IsSolvableGroupScheme
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj R) ∧
    IsNormalSubgroupScheme
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) ∧
    (∀ (N : Over (Spec (.of K))) [GrpObj N]
      (j : N ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G),
      IsClosedSubgroupScheme j → IsNormalSubgroupScheme j →
      Smooth N.hom → ConnectedSpace N.left → IsSolvableGroupScheme N →
      ∃ f : N ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj R,
        f ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i = j) := by
  sorry

end AlgebraicGeometry
