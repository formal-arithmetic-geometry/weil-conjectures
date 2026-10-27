/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.AffineLineCompositeTranspose

/-! # Counit normalization of the standing affine-line comparison

Source: projection-purity agreement, final paragraph, one-coordinate transpose.
(blueprint: lem-pur-affine-line-standing-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

/-- Inverse-transposing the standing line comparison gives its independently defined
coefficient evaluation, including canonical change of compactification.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, final paragraph, and the expanded
ordered-transpose proof, Steps 3--4
(blueprint: lem-pur-affine-line-standing-transpose).

Proof: expand affineLinePurityComparison as specifiedExceptionalHomEquiv applied to
augmentation. Its inverse Hom chain cancels each of its four factors, yielding that
augmentation in the chart compactification. The right-adjoint uniqueness comparison
lineExceptionalIso is adjunction-preserving: its inverse transpose is the canonical
left compactification comparison. At the retained lineWitness this comparison is
changeSupport, since both are transported from the same ordinary proper/open map.
Precomposition with lineSource_obj_eq changes only source coordinates. This is exactly
standingEvaluation. Boundedness follows from source_plus and the specified exceptional
boundedness theorem. The calculation uses no inverse of the line comparison, and applies
to zero coefficients and empty schemes. -/
theorem lineComparison_counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    (AffineLineEvaluation.support P aY (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (lineComparison P Y aY K Ke hKe eK) ≫
      AffineLineEvaluation.counit P aY (AffineSpace PUnit.{u + 1} Y ↘ Y) K =
    AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK := by sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
