/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.IntegralMatrixAnalyticData

/-! # Scheme naturality of the canonical continuous coefficient chart -/

@[expose] public section
universe u
open CategoryTheory Limits Opposite MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical continuous coefficient chart commutes with scheme direct image.

Source: Bhatt--Scholze, Section 6.8, continuous coefficient realization.
(blueprint: lem-weil-pbc-continuous-chart-scheme-naturality)

Proof: apply the adjunction from condensed coefficients to sheaves over X to the
asserted equality. The coefficient pushforward is the mate of the inverse-image
composition isomorphism. Compatibility of units with this composition identifies
the left adjoint with the adjoint chart over Y, followed by the inverse of the
pushforward composition comparison. The right adjoint is the chart over X followed
by the sectionwise continuous-function pushforward. On a relative profinite test
object, both expressions precompose the same continuous function with the first
projection from the same iterated scheme pullback. Pullback pasting identifies those
projections. Thus the adjoints agree on every test object and every section, and
injectivity of the adjunction Hom equivalence gives the desired equality.
No total disconnectedness, matrix, module morphism, or cokernel hypothesis is needed. -/
theorem continuousChart_scheme_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] :
    condensedPushforwardHom (Profinite.continuousMapRingObj O) f ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (chartComparison Y O) =
    chartComparison X O ≫ continuousFunctionPushforward f O := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
