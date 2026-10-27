/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.ClosedIntersectionAugmentedRow

/-! Geometry of finite closed intersections and of the base-changed family. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ClosedIntersection

/-- Finite closed intersections remain closed with quasi-compact complementary opens,
and factor through the augmentation scheme. The input family and its complement
hypotheses are stable under arbitrary scheme base change.

Source: the finite-intersection geometric deduction in step 1 of
lem-sfb-closed-intersection-vertex-contraction.
(blueprint: lem-sfb-closed-intersection-geometry).

Proof: For a nonempty finite index set, induct on its cardinality. A singleton
product in schemes over X is the member itself; adjoining an index is a fibre
product with that member. Closed immersions are stable under base change and
composition, so each structural map is closed. Its range is the intersection of
the member ranges: the two-factor equality follows from the surjectivity onto
compatible pairs of points of a scheme fibre product, and induction gives the
finite equality. Its complementary open is therefore the finite union of the
given complementary opens. On every affine open of X those opens are compact,
so their finite union is compact. This proves quasi-compactness of the union
immersion. Choose one member of a nonempty index; the product projection followed
by its given factorization gives the factorization through Z. At the empty index
the intersection is Z and the identity supplies its factorization.
For base change by g, closedness of each member follows from closed-immersion
base change. Pull back each factorization using the universal property of the
pullback; it remains a morphism over the new base. The complementary open is the
inverse image by g of the original complementary open, since the range of the
closed pullback projection is the inverse image of the original closed range.
Its immersion is the base change of the original open immersion, hence is
quasi-compact. This also gives the complement hypothesis for the augmentation.
These arguments apply to empty members and to an empty family as well. -/
theorem closed_intersection_geometry {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {m : ℕ} (W : Fin m → Over X)
    (hclosed : ∀ a, IsClosedImmersion (W a).hom)
    (hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i))
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (hqcW : ∀ a, ∃ U : X.Opens,
      Set.range U.ι = (Set.range (W a).hom)ᶜ ∧ QuasiCompact U.ι) :
    (∀ s, IsClosedImmersion (intersection i W s).hom ∧
      Nonempty (intersection i W s ⟶ Over.mk i) ∧
      ∃ U : X.Opens,
        Set.range U.ι = (Set.range (intersection i W s).hom)ᶜ ∧ QuasiCompact U.ι) ∧
    ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
      (∀ a, IsClosedImmersion (finiteClosedPullbackFamily W g a).hom) ∧
      (∀ a, Nonempty (finiteClosedPullbackFamily W g a ⟶ Over.mk (pullback.fst g i))) ∧
      (∃ U : Y.Opens, Set.range U.ι = (Set.range (pullback.fst g i))ᶜ ∧
        QuasiCompact U.ι) ∧
      (∀ a, ∃ U : Y.Opens,
        Set.range U.ι = (Set.range (finiteClosedPullbackFamily W g a).hom)ᶜ ∧
          QuasiCompact U.ι) := by sorry

end AlgebraicGeometry.ClosedIntersection
