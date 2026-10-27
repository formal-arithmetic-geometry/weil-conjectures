/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-! # Finite point fibres of an affine chart over a relatively quasi-separated space

Source: Stacks Project, Decent Spaces, Tags 03JV(1) and 03JX; Properties of Spaces,
Tag 03W7 (blueprint: lem-sfb-relative-qs-affine-chart-point-fibres).

The relation scheme is specified by its representing Yoneda pullback square. This permits
any scheme representing the sheaf fibre product, with its two actual projections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine representable étale chart mapping into an affine base open has finite
point fibres, as does its relation scheme, if the relative diagonal is quasi-compact.
Source: Stacks Project, Decent Spaces, Tags 03JV(1) and 03JX; Properties of Spaces,
Tag 03W7 (blueprint: lem-sfb-relative-qs-affine-chart-point-fibres).

Proof:
1. If x is outside the chart image, both fibres are empty. Otherwise choose w over x
   and its residue-field representative T = Spec F → W → X, using
   def-a1-algebraic-space-point-classes and def-weil-affine-spectrum. It represents x;
   no monomorphism or quasi-compactness of T → X is assumed.
2. Both W and T map into the given affine open V of S. Thus B = W ×_S T = W ×_V T
   is affine by lem-weil-pbc-fibre-product-affine-spectra, hence quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs. The scheme P = W ×_X T maps to B by a scheme test
   of the relative diagonal, so P is quasi-compact. It is étale over T by
   def-trf-algebraic-space and lem-trf-space-fibre-products-etale-covers.
3. By lem-weil-pbc-etale-fibre-discrete-separable-points over the unique point of T,
   P is discrete. Its singleton open cover has a finite subcover, so it has finitely
   many points. By lem-a1-space-point-open-calculus, their image in W is precisely
   the fibre over x. This proves the first clause.
4. The affine scheme T is quasi-separated. By lem-weil-pbc-qcqs-morphism-permanence,
   P → T and its base change Q = P ×_T P → P are quasi-compact, so Q is quasi-compact.
   The latter map is étale by lem-weil-pbc-etale-base-change-finite-limits, and Q → T
   is étale by lem-weil-pbc-etale-composition-cancellation. The same discrete-fibre
   argument shows that Q has finitely many points.
5. On test schemes, Q and R ×_X T both consist of triples (w₁,w₂,t) satisfying
   a(w₁) = a(w₂) = j(t), by lem-trf-space-fibre-products-etale-covers. This identifies
   them compatibly with projection to R. The image formula of
   lem-a1-space-point-open-calculus identifies their image in R with the second
   asserted fibre. It is finite as the image of the finite point set of Q.
   If P is empty, Q and both asserted fibres are empty as well. -/
theorem relative_qs_affine_chart_point_fibres {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hdiag : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (W : Over S) [IsAffine W.left] (a : yoneda.obj W ⟶ X.obj.obj)
    (ha : IsEtale a)
    (hbase : ∃ V : S.Opens, IsAffineOpen V ∧
      ∃ b : W.left ⟶ V.toScheme, b ≫ V.ι = W.hom)
    (R : Over S) (s t : R ⟶ W)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) a a) :
    ∀ x : Point X.obj.obj,
      Set.Finite {w : W.left | schemePointMap a w = x} ∧
        Set.Finite {r : R.left | schemePointMap (yoneda.map s ≫ a) r = x} := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
