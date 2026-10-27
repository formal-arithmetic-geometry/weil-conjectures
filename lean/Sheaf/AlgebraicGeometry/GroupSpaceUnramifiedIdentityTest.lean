/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Detecting unramified group spaces at the identity

Source: Stacks Project, spaces-groupoids.tex, Tag 0DSI,
lemma-group-scheme-unramified-or-lqf, unramified clause
(blueprint: lem-sfb-group-space-unramified-identity-test).

A group object in sheaves over the base has the multiplication on the actual sheaf
fibre product, an identity section and inversion. The condition at an identity point
is expanded as an open algebraic-space neighbourhood with unramified restriction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type group algebraic space is unramified exactly when it is
unramified at every point of its identity section.
Source: Stacks Project, Tag 0DSI, lemma-group-scheme-unramified-or-lqf
(blueprint: lem-sfb-group-space-unramified-identity-test).

Proof:
1. By lem-sfb-space-unramified-locus-base-change, the unramified locus W is the
largest open with unramified restriction, has exactly the unramified points, and
commutes with arbitrary base change. The forward implication follows immediately.
2. For the converse, represent an arbitrary point x of G by g : Spec K → G and
base change along qg. The fibre product exists by
lem-trf-space-fibre-products-etale-covers. The resulting group H over K has the
K-point (g,id), and its identity maps into W by the assumption. Its unramified locus
is the inverse image of W, by lem-sfb-space-unramified-locus-base-change.
3. Left translation by (g,id) is a natural automorphism of H, with inverse given by
translation by its inverse. It sends the identity to (g,id). Transporting an open
neighbourhood along this automorphism preserves the etale chart test for
unramifiedness (def-trf-algebraic-space, def-weil-unramified-morphism and
def-weil-open-immersion). Thus (g,id) belongs to the unramified locus of H.
4. Hence x belongs to W. Since every point does, the open immersion W → G becomes
an open immersion with full point image on each scheme chart, hence an isomorphism
(def-weil-open-immersion). Therefore q is unramified. This uses arbitrary
field-valued representatives, with no rationality or commutativity hypothesis. -/
theorem groupSpace_unramified_iff_identity {S : Scheme.{u}} (B G : AlgebraicSpace S)
    (q : G ⟶ B)
    (group : @GrpObj (Over B.obj) inferInstance (Over.cartesianMonoidalCategory B.obj)
      (Over.mk q.hom))
    (hq : MapIsLocally (@LocallyOfFiniteType) q) :
    MapIsLocally (@AlgebraicGeometry.IsUnramified) q ↔
      ∀ b : Point B.obj.obj,
        ∃ (V : AlgebraicSpace S) (i : V ⟶ G),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) i.hom.hom ∧
          mapPoint group.one.left.hom b ∈ pointImage i.hom.hom ∧
          MapIsLocally (@AlgebraicGeometry.IsUnramified) (i ≫ q) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
