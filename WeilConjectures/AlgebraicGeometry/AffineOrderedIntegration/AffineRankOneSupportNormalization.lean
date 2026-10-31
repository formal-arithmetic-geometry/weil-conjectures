/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction

/-! # Rank-one compact-support normalization

Source: projection-purity agreement, final paragraph: normalized last-line evaluation.
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

attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
  etaleCategory proCategory sourceEtale

attribute [local semireducible] sourceWitness
attribute [local implicit_reducible] sourceWitness rightDerivedLowerShriek
  Etale.affineTraceOpenLeft affineTraceLineCompactification
  affineTraceTower affineTraceProjection

set_option maxHeartbeats 3200000 in
-- Elaborating the concrete derived-source comparison requires the larger limit.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- Rank-one ordered compact support is the fixed chart compact support, on every
bounded-below ordinary source.

Source: projection-purity agreement, final paragraph, compactification coherence
(blueprint: lem-pur-affine-rank-one-support-normalization).

Proof: expand ordinaryCompactComparison at one into the bounded-below tower
comparison and its inclusion comparisons. Its successor consists of chart-to-standing
refinement followed by the rank-zero comparison and the compact-support composition
isomorphism. The right identity law for that compositor cancels the zero comparison.
The resulting change of compactification is the inverse of the fixed etale origin
comparison. Compact-support site coherence, including the equality of arrows q and
q followed by identity, moves this change past the site comparison. Normalize the
fixed site comparison to the canonical proper/open comparison. Cancel the adjacent
inclusion and refinement isomorphisms. No Tate source or counit occurs. -/
theorem rankOne_support_normalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (W : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} Y).smallEtaleTopology
      (ModuleCat.{u + 1} (AffineLinePurity.Ring P)))) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
      HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
    let A := AffineLinePurity.Ring P
    (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A)
        (Category.comp_id (lastProjection Y 0)).symm).hom.app
          ((comparison A (iteratedAffineLine Y 1)).obj W.obj) ≫
      (compactSupportSiteComparison A (compactification Y 1)).hom.app W ≫
      (comparison A Y).map
        ((Etale.rightDerivedLowerShriekIso A (compactification Y 1)).hom.app W.obj ≫
          (ordinaryCompactComparison A Y 1 W).inv) =
      (fixedCompactSupportOriginIso A
        (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))
        (affineTraceLineCompactification Y)).hom.app W ≫
      (fixedCompactSupportComparisonIso A (affineTraceLineCompactification Y)).hom.app W := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
