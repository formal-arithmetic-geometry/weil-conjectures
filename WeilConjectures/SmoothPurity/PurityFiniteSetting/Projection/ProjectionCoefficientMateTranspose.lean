/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionTensorOrdinaryData

/-! # The standing transpose of ordinary coefficient integration

Source: projection purity agreement, coefficient counit and site normalization.
(blueprint: lem-pur-projection-coefficient-mate-transpose)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale ProEtale.AffineSpacePurity ProEtale.VectorIntegrationSite

/-- The compared adjunct of the ordered coefficient trace is its standing
exceptional transpose, in the prescribed source and target coordinates.
There is only the integration exponent here: no diagonal coefficient, root
transition, unit integration mate or smooth tensor arrow occurs.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, coefficient tensor calculation and
final ordered integrations; steps 4 and 7 of lem-route-projection-tensor-integration.
(blueprint: lem-pur-projection-coefficient-mate-transpose)

Proof: source_applicability and source_origin supply the bounded ordinary tensor
representative and its bounded proetale realization. Rewrite the ordinary
coefficient trace in coefficient-first form by naturality of the braiding and
the identity relating braiding with the left and right unitors. The ordinary
counit formula identifies this evaluation with the counit of the ordered affine
adjunction in its actual ordinary source coordinates. Compare this particular
evaluation with the standing evaluation: at the first line use
lineComparison_counit and its ordinary line counit normalization; at each
successor use orderedEvaluation_contraction, the compact-support comparison
composition square and projection composition. The ordinary composite-counit
formula identifies the resulting ordered ordinary evaluation. Write J for the ordinary tensor
source, r for realizeTensorSource, B for the
legacy rightDerivedLowerShriekComparisonIso component at J, and a for
ordinaryCoefficientTrace. The resulting particular evaluation equation is
Rf!(r.hom) followed by augmentation = B.hom followed by C_Y(a) then e.hom.
Thus inverse standing transposition of the compared ordinary adjunct is precisely
augmentation after the support image of this source realization. This uses the
normalization of these particular evaluations, without asserting a universal
equality of the legacy and canonical compact-support comparison isomorphisms.
Apply the standing exceptional Hom bijection and use its source naturality.
On a compared ordinary source its Hom chain is the comparison image of the
ordinary adjunct followed by comparison of f! applied to eta_H then Rnu_*(e).
This follows directly by cancelling the two adjunction Hom bijections; the
comparison triangle identifies the last map with that literal unit composite.
These are exactly the factors of projectionCoefficientMate. At positive rank
projectionTargetMap is identity and sourceRealization supplies the specified
ordered source. At rank zero the ordinary trace and adjunction are identities;
the ordinary exceptional identity and comparison counit in projectionTargetMap
cancel the comparison unit by the triangle, leaving sourceRealization followed
by identity, which is integrationTranspose at zero. Zero coefficients and empty
bases satisfy the same unit and counit identities. -/
-- STATEMENT-DISPUTED: integrationTranspose inverts the standing counit
-- rightDerivedUpperShriekCounit, whose rightDerivedLowerShriekComparisonIso factor
-- contains an isomorphism chosen from a bare Nonempty
-- (nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar). The left side uses
-- only specified comparisons. Replacing the chosen isomorphism by its negative keeps
-- every hypothesis and negates one side, so the equation is not provable from the
-- current definitions. lineComparison_counit (step 2) carries the same marker. The
-- statement holds once that comparison is normalized to the specified proper/open
-- counit mate. The original projection_tensor_integration had the same dependency.
theorem projection_coefficient_mate_transpose
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring (projectionSetting F C E n)) Y)
    (H : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (hH : etaleFiniteTor (projectionSetting F C E n).Coefficient Y H)
    (e : (comparison (projectionSetting F C E n).Coefficient Y).obj H ≅ K.obj) (d : ℕ) :
    let P := projectionSetting F C E n
    projectionCoefficientMate F C E n Y aY K.obj H e d ≫
        projectionTargetMap F C E n Y aY K.obj d =
      (projectionOrdinarySourceRealization F C E n Y K.obj H e d).hom ≫
        ProEtale.AffineOrderedIntegration.integrationTranspose P Y aY K H hH e d := by sorry

end WeilConjectures.PurityFiniteSetting
