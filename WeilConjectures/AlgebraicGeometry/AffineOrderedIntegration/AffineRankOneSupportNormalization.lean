/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineRankOneEtaleTransport
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.CompactSupportSiteComparisonCongr
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization

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

private theorem ordinaryCompactComparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    (M : DerivedCategory.Plus
      (Sheaf (affineTraceTower Y d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ordinaryCompactComparison A Y d M =
      (Etale.affineTraceUnboundedCompactComparison A Y d).app M.obj := by
  apply Iso.ext
  change (Etale.affineTracePlusCompatibility A Y d).inv.app M ≫
    DerivedCategory.Plus.ι.map
      ((Etale.affineTraceCompactSupportComparison A Y d).hom.app M) ≫
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection Y d)).hom.app M =
    (Etale.affineTraceUnboundedCompactComparison A Y d).hom.app
      (DerivedCategory.Plus.ι.obj M)
  apply (cancel_epi ((Etale.affineTracePlusCompatibility A Y d).hom.app M)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (Etale.affineTraceUnboundedCompactComparison_restriction A Y d M).symm

private theorem pasteMaps {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {a b : D} {x₀ x₁ x₂ x₃ x₄ : C}
    (f : a ⟶ b) (s : b ⟶ F.obj x₂) (t : a ⟶ F.obj x₀)
    (e₁ : x₀ ⟶ x₁) (e₂ : x₁ ⟶ x₂) (j : x₂ ⟶ x₃) (k : x₃ ⟶ x₄)
    (h : f ≫ s = t ≫ F.map (e₁ ≫ e₂)) :
    f ≫ s ≫ F.map (j ≫ k) = t ≫ F.map (e₁ ≫ e₂ ≫ j ≫ k) := by
  rw [← Category.assoc, h]
  simp only [Functor.map_comp, Category.assoc]

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
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  dsimp only
  rw [ordinaryCompactComparison_eq]
  simp only [fixedCompactSupportOriginIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc]
  rw [compactSupportComparisonNormalization, compactSupportComparisonNormalization]
  rw [Iso.inv_hom_id_app]
  simp only [Category.comp_id]
  let A := AffineLinePurity.Ring P
  let : HasCompactification (iteratedAffineLineProj Y 1) := (projection_geometry Y 1).2
  let : IsAffineHom (lastProjection Y 0) := inferInstance
  let : QuasiCompact (lastProjection Y 0) := inferInstance
  let : QuasiCompact (𝟙 Y) := inferInstance
  let : QuasiCompact (iteratedAffineLineProj Y 1) := by
    change QuasiCompact (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0))
    exact quasiCompact_comp (lastProjection Y 0) (𝟙 (iteratedAffineLine Y 0))
  let hq : lastProjection Y 0 = iteratedAffineLineProj Y 1 :=
    (Category.comp_id (lastProjection Y 0)).symm
  let : IsNoetherian (AffineSpace PUnit.{u + 1} Y) := affineTraceNoetherian Y 1
  let : IsNoetherian (iteratedAffineLine Y 1) := affineTraceNoetherian Y 1
  let : IsNoetherian (iteratedAffineLine Y 0) := tower_noetherian P Y aY 0
  let : IsNoetherian (AffineSpace PUnit.{u + 1} (iteratedAffineLine Y 0)) :=
    affineTraceNoetherian Y 1
  have hs := compactSupportSiteComparison_congr A hq W
  have hs' :
      (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A)
          (Category.comp_id (lastProjection Y 0)).symm).hom.app
          ((comparison A (iteratedAffineLine Y 1)).obj W.obj) ≫
        (compactSupportSiteComparison A (compactification Y 1)).hom.app W =
      (compactSupportSiteComparison A
          (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))).hom.app W ≫
        (comparison A Y).map
          ((Etale.rightDerivedLowerShriekIso A
            (HasCompactification.compactification
              (AffineSpace PUnit.{u + 1} Y ↘ Y))).hom.app W.obj ≫
            (Etale.rightDerivedLowerShriekCongr A hq).hom.app W.obj) := by
    simpa only [compactification, lastProjection, iteratedAffineLineProj, iteratedAffineLine,
      Category.comp_id] using hs
  have ht := affineTrace_rankOne_etale_transport A Y W
  have hp := pasteMaps (comparison A Y) _ _ _ _ _
    ((Etale.rightDerivedLowerShriekIso A (compactification Y 1)).hom.app W.obj)
    ((Etale.affineTraceUnboundedCompactComparison A Y 1).inv.app W.obj) hs'
  have hh := congrArg (fun z ↦
    (compactSupportSiteComparison A
      (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))).hom.app W ≫
        (comparison A Y).map z) ht
  exact hp.trans hh

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
