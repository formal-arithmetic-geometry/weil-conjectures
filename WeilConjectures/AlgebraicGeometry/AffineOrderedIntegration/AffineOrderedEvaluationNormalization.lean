/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitZero
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitSuccessor
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Ordinary-counit normalization of ordered tensor integration
Source: projection-purity agreement, final paragraph, ordered counit calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local semireducible] ordinarySourceObject
attribute [local implicit_reducible] ordinarySourceObject
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor Etale.rightDerivedLowerShriek
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  ordinaryLower sourceEtale etaleCategory proCategory

set_option maxHeartbeats 800000 in
-- Identifying the concrete derived source functors needs additional elaboration.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- The tensor augmentation in explicit ordinary counit coordinates, at one rank.
This statement contains no last-coordinate evaluation or compact-support composition.
Source: current blueprint projection-purity agreement, final paragraph.
(blueprint: lem-pur-affine-ordered-evaluation-normalization).

Proof step 1: For every finite-Tor ordinary H prove OrdinaryCounitEquation at all d by
induction: ordinary_counit_zero is the base, and ordinary_counit_successor applies the induction
hypothesis to all finite-Tor H. This gives the coefficient-first tensor formula for the actual
bounded-below transported counit, rather than replacing it by an unbounded or product-coordinate
counit.

Proof step 2: Insert the exact-versus-left-derived pullback tensor isomorphism into that
equation and cancel its inverse. By definition the remaining source/counit factors are
ordinaryTensorCoordinatesRaw.hom followed by ε_d. Transport the equality along
affineTower_projection_eq, including the proof-irrelevant compactifiability witnesses. The HEq
characterizations of ordinaryTensorCoordinates and ordinaryTrace give the corresponding equation
on the iteratedAffineLine tower. Identity-refinement coherence identifies the standing ordinary
compactification comparison with identity.

Proof step 3: Write W for the ordinary rank-d Tate coefficient, J=p_d^*Ke⊗W, C_W,C_J for
compact-support site comparisons, V for comparison on Y, and b for tensorPullbackComparison on
X_d. The boundedness hypotheses for W and J follow from source_applicability. Apply the
compact-support projection square. Naturality of the signed braiding on both sites puts it in
coefficient-first order. If P_e and P_p are the actual ordinary and pro-etale projections, the
square becomes δ_(Ke,FeW);(1⊗C_W.inv);P_p = V(P_e);C_J.inv;F_d(b.hom). The exact-pullback
comparison appearing in the ordinary formula is cancelled by its inverse. Its cancellation uses
symmetry naturality and the involutivity of the actual canonical signed swap, not an unspecified
tensor isomorphism.

Proof step 4: Invert the two projection isomorphisms in this square. Tensor-comparison
naturality for the ordinaryTrace map moves tensor with that trace across δ. The definition of
integration says C_W.inv;integration=V(ordinaryTrace), after identity compactification
comparison. The coefficient-unit comparison is the derived oplax unit; therefore oplax
right-unitality identifies moduleRightUnit with δ.inv followed by V of the ordinary right
unitor. The ordinary single-unit identification is identity, so the ordinaryFiniteTensorTrace
formula has precisely that right unitor. Thus F_d(b.hom);augmentation_(VKe) =
C_J.hom;V(ordinaryTensorCoordinates.hom;ε_d).

Proof step 5: Projection-map naturality, inversion of the projection, tensor bifunctoriality and
right-unitor naturality show naturality of projectionTensorTrace in eK.hom. Use this to replace
VKe by K in the preceding equation. Expand sourceRealization=realizeTensorSource followed by
s_d.symm. Its inverse, the site comparison C_J and the ordinary coordinates are exactly E_d.
Cancellation of realizeTensorSource and associativity give the claimed equation. All maps exist
on zero coefficients and the empty base; d=0 uses the specified inverse tensor unitor and
identity pullback. -/
theorem orderedEvaluation_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y d)).map
        (sourceComparison P Y K.obj d).hom ≫ augmentation P Y aY K Ke hKe eK d =
      (orderedCounitCoordinates P Y aY K Ke hKe eK d).hom ≫
        (comparison (AffineLinePurity.Ring P) Y).map
          ((orderedAdjunction P Y aY d).counit.app Ke) ≫ eK.hom := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
