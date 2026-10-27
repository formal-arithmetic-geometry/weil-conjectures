/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Topology.Defs.Filter
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.ChartPairFiniteResidualRelation
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite chart and relation fibres give quasi-compact field representatives

Source: Stacks Project, Decent Spaces, Tag 03JV (lemma-UR-finite-above-x),
implication (2) to (6)
(blueprint: lem-sfb-finite-chart-fibres-field-quasicompact).

Scheme fibre products are specified by their representing Yoneda pullback squares.
The conclusion tests every affine scheme mapping to the space, without an étale condition.
-/

@[expose] public section

universe u w

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- If the fibres over `x` in an étale scheme covering and its self-relations are finite,
every field-valued representative of `x` is quasi-compact. The charts need not be affine
or quasi-compact, and their individual fibres may be empty.
Source: Stacks Project, Decent Spaces, Tag 03JV (lemma-UR-finite-above-x), (2) to (6)
(blueprint: lem-sfb-finite-chart-fibres-field-quasicompact).
Proof:
1. Apply [lem-sfb-space-change-base-to-integers] to view the space over `Spec ℤ`.
The scheme charts, their relations, point classes and relevant fibre products are unchanged.
Every original affine test is also an absolute affine test, so the absolute conclusion
implies the original one.
2. By [lem-sfb-etale-chart-finite-fibre-transfer], finiteness of the given chart fibres
implies finiteness above `x` in every affine representable étale chart `V → X`.
3. Joint surjectivity supplies one chart point `u` above `x`. The relation fibre above
`(u,u)` is contained in the assumed finite relation fibre above `x`. Thus
[lem-sfb-chart-pair-finite-residual-relation] makes both projections of the residual
self-relation étale and quasi-compact. Apply
[lem-sfb-finite-point-self-relation-field-monomorphism] to obtain a field monomorphism
`j : Spec k → X` representing `x`.
4. For each affine étale chart `V`, let `D = V ×_X Spec k`. The projection `D → V`
is monic by monomorphy of `j` and the pullback universal property
[lem-trf-space-fibre-products-etale-covers]. The field-point criterion
[def-weil-radicial-morphism] makes it universally injective, hence injective on points.
Its image lies in the finite chart fibre above `x`, so `D` has finitely many points.
5. The map `D → Spec k` is étale. By
[lem-weil-pbc-etale-fibre-discrete-separable-points], `D` is a disjoint union of spectra
of finite separable extensions, indexed by its finite point set. By
[lem-weil-pbc-spec-finite-product-fields], it is the spectrum of their finite product.
Concatenating finite bases makes this product finite-dimensional, so the morphism is
finite [def-weil-finite-integral-morphism]; the empty case uses the zero algebra.
Finally [lem-sfb-field-monomorphism-finite-chart-decency-criterion] gives quasi-compactness
of every field representative on every affine test, and step 1 returns to the original base. -/
theorem finite_chart_fibres_field_quasicompact {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Point X.obj.obj) {I : Type w} (U : I → Over S)
    (a : ∀ i : I, yoneda.obj (U i) ⟶ X.obj.obj)
    (ha : ∀ i : I, IsEtale (a i))
    (hcover : ∀ y : Point X.obj.obj, ∃ (i : I) (v : (U i).left),
      schemePointMap (a i) v = y)
    (R : I → Over S) (p₁ p₂ : ∀ i : I, R i ⟶ U i)
    (hR : ∀ i : I, IsPullback (yoneda.map (p₁ i)) (yoneda.map (p₂ i)) (a i) (a i))
    (hU : ∀ i : I, Set.Finite {v : (U i).left | schemePointMap (a i) v = x})
    (hfinite : ∀ i : I, Set.Finite {r : (R i).left |
      schemePointMap (yoneda.map (p₁ i) ≫ a i) r = x}) :
    ∀ c : PointRepresentative X.obj.obj, Quot.mk _ c = x →
      ∀ (T : Over S), IsAffine T.left → ∀ t : yoneda.obj T ⟶ X.obj.obj,
        ∃ (V : Over S) (p : V ⟶ T) (q : V ⟶ Over.mk c.base),
          IsPullback (yoneda.map p) (yoneda.map q) t (yonedaEquiv.symm c.value) ∧
            CompactSpace V.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
