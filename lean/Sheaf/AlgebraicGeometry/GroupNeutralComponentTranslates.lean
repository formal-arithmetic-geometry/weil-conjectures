/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent

/-!
# Connected components of finite type group schemes

Source: Stacks Project, Tag 0B7R; Milne, Algebraic Groups (2017), Proposition 1.34,
Corollary 1.35 and the dimension discussion before Proposition 1.37, pp. 16-18
(blueprint: lem-sfb-group-neutral-component-translates).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

/-- The identity component with its open subscheme structure is a clopen closed subgroup,
and every connected component is a rational left translate of it as a scheme over the base.
Source: Stacks Project, Tag 0B7R; Milne, Algebraic Groups (2017), Proposition 1.34,
Corollary 1.35 and pp. 16-18
(blueprint: lem-sfb-group-neutral-component-translates).

Proof:
1. Apply lem-sfb-locally-algebraic-group-identity-component. Its clopen identity component
has the open subscheme structure used by GrpObj.identityComponent. Its inclusion is also
closed (def-weil-closed-immersion): sections on its intersection with any open extend by
zero on the complementary open. The restricted group operations make it a closed subgroup.
2. Given x in a component D, its closure is connected and contained in D by maximality.
By lem-sc-lft-over-field-jacobson-space that nonempty closed subset contains a closed point.
By lem-weil-pbc-closed-point-residue-field-base the closed point has residue field k, hence
comes from a k-rational point g of D.
3. The translation t_g of def-sc-group-scheme-translate is an automorphism with inverse
translation by g inverse (lem-sc-translation-automorphism). Its homeomorphism sends the
identity component to the component of g, namely D, since it preserves connectedness and
maximality. Thus D is open, and restriction of t_g and its inverse gives inverse maps of
the open subschemes (def-weil-open-immersion). These maps retain the full structure sheaves.
4. Components cover G and distinct components are disjoint: unions of intersecting
connected sets are connected. By step 3 they form an open cover. Finite type includes
quasi-compactness (def-weil-finite-type-morphism), so there is a finite subcover. Every
component is nonempty and disjoint from the others, so this includes every component. -/
theorem GrpObj.finiteTypeGroup_neutralComponent_translates
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsClopen (connectedComponent (GrpObj.onePoint G)) ∧
      IsClosedSubgroupScheme (GrpObj.identityComponentι G) ∧
      Finite (ConnectedComponents G.left) ∧
      ∀ x : G.left, ∃ D : G.left.Opens,
        (D : Set G.left) = connectedComponent x ∧
        ∃ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
          (e : GrpObj.identityComponent G ≅ Over.mk (D.ι ≫ G.hom)),
          e.hom.left ≫ D.ι =
            (GrpObj.identityComponentι G).left ≫ (GrpObj.mulLeft G g).left := by
  sorry

end AlgebraicGeometry
