/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.DimZeroFiniteOverField
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.LinearGroupSchemes

/-!
# The centre of a general connected algebraic group

Source: Milne, Algebraic Groups (2017), Proposition 1.92 and the centre definition,
pp.33--34; Corollary 1.35 and Proposition 1.38, pp.17--18; Corollaries 8.10--8.11,
pp.150--151; Proposition 8.1(a), p.149; Theorem 8.26, first case, p.154
(blueprint: lem-sfb-general-group-centre-zero-dimension-affine).

The centralizer of the identity homomorphism is the centre subfunctor. Its
representing subgroup is allowed to be non-smooth, and the ambient group is not
assumed affine or commutative. The open `Z0` is specified by its underlying set,
so its scheme structure is the open subscheme structure, before taking reduction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The scheme-theoretic centre is a closed commutative normal subgroup; its
reduced identity component has the same dimension as the centre, and a
zero-dimensional centre forces the ambient group to be affine.

Source: Milne, Algebraic Groups (2017), Proposition 1.92, pp.33--34;
Corollary 1.35 and Proposition 1.38, pp.17--18; Corollaries 8.10--8.11,
Proposition 8.1(a), and the first case of Theorem 8.26, pp.149--154
(blueprint: lem-sfb-general-group-centre-zero-dimension-affine).

Proof plan, following the four steps of the node:
1. Apply lem-sfb-fixed-point-action-finite-jets to conjugation of G on itself,
   fixing the identity. A sufficiently high jet representation has closed normal
   finite-type kernel Z. On every algebra B its kernel points are precisely the
   elements commuting with every G(B') after every B-algebra extension. This is
   centralizerPoints of the identity homomorphism. Taking B'=B and a second
   Z-point proves commutativity, by def-sc-group-scheme-subgroup and
   def-sc-group-scheme.
2. Apply lem-sfb-group-neutral-component-translates to Z. Its identity component
   Z0 is open and closed, and its finitely many components are isomorphic translates.
   Every irreducible closed chain lies in one component, so their topological
   dimensions agree. By lem-weil-pbc-reduction-universal-homeomorphism, reduction
   preserves the underlying space and therefore its irreducible closed chains.
   Thus dim (Z0_red) = dim Z0 = dim Z.
3. If dim Z=0, use lem-pc-scheme-dimension-local-rings and
   lem-pc-algebraic-dim-zero-affine-finite to make Z affine. Factor the jet
   representation by lem-sfb-algebraic-group-homomorphism-factorization through
   a faithfully flat quotient I and a closed immersion into GL(V). The determinant
   localization of def-sc-general-linear-group is affine, and a closed subscheme
   of an affine scheme is affine by def-weil-closed-immersion. Hence I is affine.
4. The exact sequence 1 -> Z -> G -> I -> 1 has flat surjective quotient map.
   Apply the affine-extension clause of
   lem-sfb-exact-algebraic-group-property-permanence to conclude that G is affine.
   The kernel is not replaced by its reduction, so non-smooth finite centres remain. -/
theorem exists_centre_reducedIdentityComponent_dim_and_isAffine
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k))))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    ∃ (Z : Grp (Over (Spec (.of k)))) (i : Z ⟶ G) (Z0 : Z.X.left.Opens),
      IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
      IsCommMonObj Z.X ∧
      (∀ (B : Type u) [CommRing B] [Algebra k B],
        ReductiveTorusCentralizer.centralizerPoints (𝟙 G) B =
          Set.range (fun z : StandardGroupSchemes.affine k B ⟶ Z.X ↦ z ≫ i.hom.hom)) ∧
      (Z0 : Set Z.X.left) = connectedComponent (GrpObj.onePoint Z.X) ∧
      topologicalKrullDim Z0.toScheme.nilradical.subscheme = topologicalKrullDim Z.X.left ∧
      (topologicalKrullDim Z.X.left = 0 → IsAffine G.X.left) := by
  sorry

end AlgebraicGeometry
