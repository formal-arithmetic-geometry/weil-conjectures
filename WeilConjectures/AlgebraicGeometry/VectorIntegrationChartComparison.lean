/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationChartCoordinates
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.ProjectionPurityAgreement
public import WeilConjectures.AlgebraicGeometry.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSiteComparison
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.AffineSpacePurityComparison

import WeilConjectures.AlgebraicGeometry.VectorIntegrationUnitTranspose
import WeilConjectures.AlgebraicGeometry.VectorIntegrationChartTranspose
import WeilConjectures.AlgebraicGeometry.AffineIntegrationExponentTransition
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegrationTransposes

/-! # Integration-normalized vector-bundle comparison in coordinates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-amb-vector-bundle-purity.proof.md, second paragraph, together with the ordered
counit normalization in lem-amb-affine-space-top-trace.proof.md
(blueprint: lem-pur-vector-integration-chart-comparison).

The canonical coordinate constructions are imported from
`VectorIntegrationChartCoordinates`; no comparison map is chosen anew here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart

/-- The integration-normalized inverse unit-object purity comparison restricts in every
linear vector-bundle chart to the specified ordered affine-line comparison, independently
of the positive annihilating exponent. Rank zero is included.

Source: latest blueprint, sec-smooth-purity/sk-prop-an,
thm-amb-vector-bundle-purity.proof.md, second paragraph; ordered affine counit in
lem-amb-affine-space-top-trace.proof.md
(blueprint: lem-pur-vector-integration-chart-comparison).

Proof in words:
1. Use def-pur-vector-chart-comparison-coordinates. Its open_geometry and unit_properties
   supply the finite-type open base and coefficient-unit domain. The HEq specification of
   restrictedMap and lem-pur-vector-chart-restricted-affine-transpose identify the restricted
   map at every positive annihilating exponent with the ordinary affineTranspose on U.
2. At the fixed exponent, lem-pur-affine-unit-transpose-coordinates expresses that transpose
   in the canonical source and exceptional target coordinates. The first clause of
   lem-pur-affine-ordered-integration-transposes identifies its integrationTranspose with
   affineSpacePurityComparison. Their composite is exactly orderedMap.
3. Rewrite both restricted maps by step 1 and apply
   lem-pur-affine-transpose-exponent-transition. This proves the exponent-transition clause
   of ChartComparison. The identity adjunction gives rank zero, and all constructions
   apply to empty schemes as well.
-/
theorem vectorIntegration_chart_comparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d F U) :
    ChartComparison P Z aZ d F U e := by
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType aZ
  let : LocallyOfFiniteType (U.ι ≫ aZ) := (open_geometry P Z aZ U).1
  let : QuasiCompact (U.ι ≫ aZ) := (open_geometry P Z aZ U).2.1
  let : IsSeparated (U.ι ≫ aZ) := (open_geometry P Z aZ U).2.2
  let : IsNoetherian U.toScheme := isNoetherian_of_locallyOfFiniteType (U.ι ≫ aZ)
  have hrestricted (r : ℕ)
      (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : AffineLinePurity.Ring P) = 0) :
      restrictedMap P Z aZ d F U e r hA =
        affineTranspose P U.toScheme (U.ι ≫ aZ) d r hA := by
    exact eq_of_heq
      ((restrictedMap_existsUnique P Z aZ d F U e r hA).exists.choose_spec.trans
        (chartTranspose_eq_affine P Z aZ d F U e r hA))
  constructor
  · rw [hrestricted, affineTranspose_unit_coordinates]
    unfold orderedMap
    rw [(AffineOrderedIntegration.ordered_integration_transposes P U.toScheme
      (U.ι ≫ aZ) (unitPlus P U.toScheme)
      (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) U.toScheme)
      (unit_properties P U.toScheme).2 (Iso.refl _)).1 d]
  · intro r r' h hA hA'
    rw [hrestricted, hrestricted]
    exact affineTranspose_exponent_transition P U.toScheme (U.ι ≫ aZ) d r r' h hA hA'

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
