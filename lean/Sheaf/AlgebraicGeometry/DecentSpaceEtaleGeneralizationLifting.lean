/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

/-!
# Étale charts of decent algebraic spaces lift generalizations

Source: Stacks Project, Decent Spaces, Tag 03IL (lemma-decent-specialization),
with decency expressed by Tag 03JV(4)
(blueprint: lem-sfb-decent-space-etale-generalization-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Generalizations lift to generalizations of a prescribed point of an étale scheme chart.
The field representatives are monomorphic against every algebraic-space test object and
quasi-compact after every scheme test. Specialization is written as singleton closure
membership, in the atlas topology on point classes and the scheme topology on the chart.
Source: Stacks Project, Decent Spaces, Tags 03IL, 03JV(4), and 03K2
(blueprint: lem-sfb-decent-space-etale-generalization-lifting).

Proof:
1. Choose an affine neighbourhood W of u₀ by [lem-weil-pbc-affine-opens-basis]. Its map
   a to X is representable étale by [lem-weil-pbc-etale-composition-cancellation]. Its
   image I is open by [lem-a1-space-point-open-calculus], hence contains x. The scheme
   relation R = W ×_X W has étale, hence flat, projections s and t, by
   [lem-trf-space-fibre-products-etale-covers] and [def-trf-algebraic-space].
2. Pull the quasi-compact field representative of x back to W. This scheme P is
   quasi-compact since W is affine ([lem-weil-pbc-affine-scheme-qcqs]). It is étale over
   the field, so discrete by [lem-weil-pbc-etale-fibre-discrete-separable-points], using
   [def-weil-affine-spectrum] and identity base change [def-pc-fibre-product]. Therefore
   P has finitely many points. The image formula of [lem-a1-space-point-open-calculus]
   identifies its image with the nonempty finite fibre A = a⁻¹({x}).
3. Let C be the finite union of closures of points in A; it is closed. Flat generalization
   lifting [lem-weil-pbc-flat-generalizations-lift] and continuity of s and t show
   s⁻¹(C) = t⁻¹(C): lift a generalization from A along s, then apply t; interchange
   s and t for the reverse inclusion.
4. Point surjectivity for the relation [lem-a1-space-point-open-calculus] makes C
   saturated. Thus I ∖ a(C) = a(W ∖ C), which is open by the same node, so a(C) is closed
   in I.
5. Since x belongs to a(C) and specializes to a(u₀), closedness gives a(u₀) in a(C).
   Saturation implies u₀ belongs to C. Some u in A therefore specializes to u₀ in W,
   and also in U by continuity of the open inclusion, with p(u) = x. -/
theorem exists_generalization_of_decent_of_isEtale
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hdecent : ∀ x : Point X.obj.obj,
      ∃ (K : Type u) (_ : Field K) (b : Spec (CommRingCat.of K) ⟶ S)
        (i : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
        schemePointMap i (IsLocalRing.closedPoint K) = x ∧
        (∀ (Y : AlgebraicSpace S) (f g : Y.obj.obj ⟶ yoneda.obj (Over.mk b)),
          f ≫ i = g ≫ i → f = g) ∧
        IsRepresentableWith (fun _ _ q ↦ QuasiCompact q.left) i)
    (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj) (hp : IsEtale p)
    (u₀ : U.left) (x : Point X.obj.obj)
    (hx : schemePointMap p u₀ ∈ closure ({x} : Set (Point X.obj.obj))) :
    ∃ u : U.left, u₀ ∈ closure ({u} : Set U.left) ∧ schemePointMap p u = x := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
