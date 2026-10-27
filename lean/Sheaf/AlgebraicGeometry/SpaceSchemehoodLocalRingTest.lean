/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Stalk
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Schemehood tested over local rings of the base

Source: Stacks Project, Limits of Spaces, Tag 0B80 (lemma-enough-local)
(blueprint: lem-sfb-space-schemehood-local-ring-test).

Quasi-compactness uses the existing affine-test condition on point spaces. The equality
of point classes identifies the image of a point with an ordinary point of the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact quasi-separated algebraic space over a scheme is schematic if its
pullback to the local ring at the image of every point is schematic.
Source: Stacks Project, Limits of Spaces, Tag 0B80 (lemma-enough-local)
(blueprint: lem-sfb-space-schemehood-local-ring-test).

Proof:
1. Compare the point-space affine-test quasi-compactness condition with the atlas
condition: a surjective etale affine scheme atlas of any quasi-compact test space and
base change of etale covers reduce one to the other. Use lem-a1-space-etale-open-image,
lem-sfb-qc-space-affine-etale-atlas and lem-trf-space-fibre-products-etale-covers.
2. For a point x with image t, the affine open neighbourhoods W of t form a small,
nonempty directed inverse system with affine transitions and limit Spec O_{T,t}, by
lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods. Each X_W is quasi-compact
by the hypothesis on g and quasi-separated by base change and the affine base W;
use lem-sfb-space-quasiseparated-test-calculus, lem-weil-pbc-affine-scheme-qcqs and
lem-sfb-space-qcqs-source-products.
3. The maps X_W to X_V are affine by base change (lem-sfb-space-affine-locality).
On every test scheme, compatible sections are a single section of X together with
compatible maps to W. The local-ring limit property identifies these, naturally and
bijectively, with sections of X times_T Spec O_{T,t}.
4. This limit is a scheme by the local hypothesis. Apply the schematic-stage clause of
lem-sfb-space-affine-limits-schematic-stages to obtain a W for which X_W is a scheme.
5. By lem-a1-space-open-factor-scheme-tests, X_W is an open subspace containing x.
The largest schematic open (lem-sfb-space-largest-schematic-open) therefore contains
every point. The open-subspace/point-open correspondence of lem-a1-space-etale-open-image
identifies it with X. This also handles the empty point space. -/
theorem isScheme_of_local_ring_tests {S : Scheme.{u}} (T : Over S)
    (X : AlgebraicSpace S) (g : X.obj.obj ⟶ yoneda.obj T)
    (hqc : MapIsQuasiCompact g) (hqs : MapIsQuasiCompact (pullback.diagonal g))
    (hlocal : ∀ (x : Point X.obj.obj) (t : T.left),
      mapPoint g x = schemePointMap (𝟙 (yoneda.obj T)) t →
        ∃ U : Over S, Nonempty
          (Limits.pullback g
            (yoneda.map (Over.homMk
              (U := Over.mk (T.left.fromSpecStalk t ≫ T.hom))
              (V := T) (T.left.fromSpecStalk t) rfl)) ≅ yoneda.obj U)) :
    ∃ U : Over S, Nonempty (X.obj.obj ≅ yoneda.obj U) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
