/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Reduced

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Sheaf.AlgebraicGeometry.ProperDimZeroFiniteOverField
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Dimension

/-!
# Reduced identity components of closed abelian subgroups

Source: Milne, Algebraic Groups (2017), Corollary 1.35, the discussion before
Proposition 1.37, Proposition 1.38 and Corollary 1.39, pp. 17-18;
Stacks Project, Tags 047P, 047R, 0B7R and 06LH
(blueprint: lem-sfb-abelian-closed-subgroup-reduced-component).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The reduction of a closed subgroup of an abelian variety is a subgroup, and its
identity component, with the open subscheme structure, is an abelian closed subgroup
of the ambient variety. Its dimension equals that of the original subgroup, which
is finite over the field if this common dimension is zero, even when nonreduced.

Source: Milne, Algebraic Groups (2017), Corollary 1.35, the discussion before
Proposition 1.37, Proposition 1.38 and Corollary 1.39, pp. 17-18;
Stacks Project, Tags 047P, 047R, 0B7R and 06LH
(blueprint: lem-sfb-abelian-closed-subgroup-reduced-component).

The existential group structures are uniquely fixed by requiring the canonical
inclusions to be subgroup homomorphisms: both inclusions are monomorphisms.
The equality of opens fixes the component itself, with its actual structure sheaf.

Proof:
1. By [def-sc-abelian-variety], A is proper over k. Apply
   [lem-weil-pbc-closed-immersion-proper] to H → A and to the reduction G = H_red → H
   from [lem-weil-pbc-reduction-universal-homeomorphism]. Both H and G are proper,
   hence finite type by [def-weil-proper-morphism]. A field is Noetherian, so
   [lem-weil-pbc-finite-type-over-noetherian] makes G Noetherian. The reduction is reduced.
2. The algebraically closed field is perfect: in characteristic p, every element has a
   p-th root by algebraic closedness; the other case is characteristic zero. Apply
   [lem-kun-geometric-reduced-perfect] to G to obtain geometric reducedness and flatness.
   Apply [lem-sfb-flat-geometrically-reduced-pullback] with Y = T = G and S = Spec k.
   The locally Noetherian and reduced hypotheses follow from step 1, so G ×_k G is reduced.
3. Restrict the multiplication of H to G ×_k G. By step 2 and
   [lem-weil-pbc-reduced-source-factors-through-closed-subscheme], it factors through
   G → H. The same factorization applies to inversion on G and the unit from Spec k,
   which is reduced. Composing each proposed group axiom with G → H reduces it to
   the corresponding axiom of H; the closed immersion is a monomorphism, so the
   equalities hold on G itself. Thus G is a group scheme and G → H is a homomorphism,
   in the sense of [def-sc-group-scheme] and [def-sc-group-scheme-subgroup].
4. By [lem-sfb-group-neutral-component-translates], the identity component B of G
   is a connected open subscheme and a closed subgroup. Step 2 and
   [lem-sfb-geometrically-reduced-group-smooth] make G smooth. Restrict smoothness to B
   using clause (a) of [lem-weil-pbc-smooth-restrict-open-subschemes].
5. The closed inclusion B → G and properness of G give properness of B by
   [lem-weil-pbc-closed-immersion-proper]. Together with smoothness and connectedness,
   [def-sc-abelian-variety] identifies B as an abelian variety. The inclusions
   B → G → H → A compose to a closed immersion by
   [lem-weil-pbc-closed-immersion-products]; their group homomorphisms compose too.
6. By [lem-sfb-group-neutral-component-translates], G is a finite disjoint union of
   clopen components isomorphic to B by translations. An irreducible closed subset
   cannot meet both a clopen component and its complement. Every strict chain of
   nonempty irreducible closed subsets thus lies in one component, and its possible
   lengths give dim G = dim B by [def-kun-topological-krull-dimension]. The reduction
   homeomorphism of [lem-weil-pbc-reduction-universal-homeomorphism] bijects these chains
   on G and H. Consequently dim H = dim G = dim B, with no reducedness assumption on H.
7. If dim B = 0, step 6 gives topological dimension zero for H. Its unit makes it
   nonempty. Use [lem-pc-scheme-dimension-local-rings] to identify this dimension with
   the supremum of its local-ring dimensions, as in [def-pc-dimension]. Properness of H
   was established in step 1 without assuming reducedness. Apply
   [lem-pc-dim-zero-finite-over-field] to conclude that H → Spec k is finite, including
   when H is nonreduced.
-/
theorem closedSubgroup_reduced_identityComponent
    (k : Type u) [Field k] [IsAlgClosed k]
    (A H : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] [GrpObj H]
    (i : H ⟶ A) [IsClosedSubgroupScheme i] :
    ∃ gR : GrpObj (GrpObj.reduced H),
      IsClosedSubgroupScheme (GrpObj.reducedι H) ∧
      ∃ U : (GrpObj.reduced H).left.Opens,
        (U : Set (GrpObj.reduced H).left) =
          connectedComponent (GrpObj.onePoint (GrpObj.reduced H)) ∧
        ∃ gB : GrpObj (Over.mk (U.ι ≫ (GrpObj.reduced H).hom)),
          IsAbelianVariety (Over.mk (U.ι ≫ (GrpObj.reduced H).hom)) ∧
          IsClosedSubgroupScheme
            ((Over.homMk U.ι : Over.mk (U.ι ≫ (GrpObj.reduced H).hom) ⟶ GrpObj.reduced H) ≫
              GrpObj.reducedι H ≫ i) ∧
          topologicalKrullDim U.toScheme = topologicalKrullDim H.left ∧
          (topologicalKrullDim U.toScheme = 0 → IsFinite H.hom) := by
  sorry

end AlgebraicGeometry
