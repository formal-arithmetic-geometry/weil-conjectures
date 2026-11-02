/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality

/-! Rank-one affine-trace transport for compactification comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local irreducible] Etale.rightDerivedLowerShriekOfCompactificationIso
  Etale.unboundedEtaleLowerShriekCompIso Etale.unboundedEtaleLowerShriekId
attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  iteratedAffineLine iteratedAffineLineProj compactification
  Etale.rightDerivedLowerShriek

private theorem etaleCongr_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f g : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact g] [HasCompactification f] [HasCompactification g]
    (h : f = g) : Etale.rightDerivedLowerShriekCongr A h =
      Etale.unboundedEtaleLowerShriekCongr A h := by
  subst g
  exact (Etale.unboundedEtaleCompactSupport_comparison_coherence A f).1 _

private theorem finish_transport {C : Type*} [Category* C] {a b c d : C}
    (i : a ≅ c) (e : b ≅ c) (g : c ≅ d) (j : d ≅ d) (v : b ≅ d)
    (t : a ⟶ b) (hj : j = Iso.refl d)
    (hv : v.hom = e.hom ≫ g.hom) (ht : t ≫ e.hom = i.hom) :
    i.hom ≫ g.hom ≫ j.hom ≫ v.inv = t := by
  subst j
  simp only [Iso.refl_hom, Category.id_comp]
  apply (cancel_mono v.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hv, ← Category.assoc, ht]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
-- The concrete derived-functor endpoints need a larger elaboration budget.
/-- The rank-one unbounded affine-trace comparison transports the chosen compactification
comparison to the standard projective-line compactification.

Source: Stacks Tags 0F7I and 0F7K; the ordered normalized affine-line iteration in
projection-purity agreement, final paragraph
(blueprint: lem-pur-affine-rank-one-etale-transport).

Proof: expand the successor formula for the unbounded affine-trace comparison at rank
one. Its rank-zero factor is the inverse identity comparison. The compositor right-unit
law gives the identity comparison followed by the congruence q=q≫id, so the rank-zero
inverse cancels. The remaining map is the standard-line-to-chosen compactification
comparison followed by the congruence. The self-comparison of the chosen q≫id
compactification is the identity. Equality induction and the compactification identity
law identify the two existing versions of etale congruence. Finally the bounded-below
restriction theorem and the compactification cocycle law show that change from the
chosen q compactification to the standard line, followed by its chosen comparison,
is the chosen q self-comparison. Cancel the rank-one isomorphism to obtain the result.
No nonempty-scheme or nonzero-complex assumption occurs. -/
theorem affineTrace_rankOne_etale_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y]
    [HasCompactification (AffineSpace PUnit.{u + 1} Y ↘ Y)]
    [QuasiCompact (AffineSpace PUnit.{u + 1} Y ↘ Y)]
    [HasCompactification (iteratedAffineLineProj Y 1)]
    [QuasiCompact (iteratedAffineLineProj Y 1)]
    (W : DerivedCategory.Plus
      (Sheaf (AffineSpace PUnit.{u + 1} Y).smallEtaleTopology
        (ModuleCat.{u + 1} A))) :
    (Etale.rightDerivedLowerShriekIso A
        (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))).hom.app W.obj ≫
      (Etale.rightDerivedLowerShriekCongr A
        (Category.comp_id (AffineSpace PUnit.{u + 1} Y ↘ Y)).symm).hom.app W.obj ≫
      (Etale.rightDerivedLowerShriekIso A (compactification Y 1)).hom.app W.obj ≫
      (Etale.affineTraceUnboundedCompactComparison A Y 1).inv.app W.obj =
    (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A
        (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))
        (affineTraceLineCompactification Y)).hom.app W := by
  let q := AffineSpace PUnit.{u + 1} Y ↘ Y
  let : IsNoetherian (AffineSpace PUnit.{u + 1} Y) := affineTraceNoetherian Y 1
  have hu := congr_app (Etale.unboundedEtaleLowerShriekCompIso_units A q).2 W.obj
  have hU : (Etale.affineTraceUnboundedCompactComparison A Y 1).hom.app W.obj =
      (Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification Y)).hom.app
        W.obj ≫
      (Etale.unboundedEtaleLowerShriekCongr A (Category.comp_id q).symm).hom.app W.obj := by
    change (Etale.rightDerivedLowerShriekIso A
      (affineTraceLineCompactification Y)).hom.app W.obj ≫
      (Etale.unboundedEtaleLowerShriekId A Y).inv.app
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj W.obj) ≫
      (Etale.unboundedEtaleLowerShriekCompIso A q (𝟙 Y)).hom.app W.obj = _
    rw [hu]
    simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.rightUnitor_hom_app,
      Iso.inv_hom_id_app_assoc]
    erw [Category.id_comp]
  let : IsNoetherian (iteratedAffineLine Y 1) := affineTraceNoetherian Y 1
  have hself : Etale.rightDerivedLowerShriekIso A (compactification Y 1) = Iso.refl _ :=
    (Etale.unboundedEtaleCompactSupport_comparison_coherence A
      (iteratedAffineLineProj Y 1)).1 _
  let c₀ := HasCompactification.compactification q
  let c₁ := affineTraceLineCompactification Y
  have hb : (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c₀ c₁).hom.app W =
      (Etale.rightDerivedLowerShriekOfCompactificationIso A c₀ c₁).hom.app W.obj := by
    change (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c₀).inv.app W ≫
      DerivedCategory.Plus.ι.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c₀ c₁).hom.app W) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c₁).hom.app W = _
    rw [Etale.unboundedEtaleCompactSupport_comparison_plus A q c₀ c₁ W]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have hc := congrArg (fun z ↦ z.hom.app W.obj)
    ((Etale.unboundedEtaleCompactSupport_comparison_coherence A q).2
      c₀ c₁ (HasCompactification.compactification q))
  have hp : (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c₀ c₁).hom.app W ≫
      (Etale.rightDerivedLowerShriekIso A c₁).hom.app W.obj =
      (Etale.rightDerivedLowerShriekIso A c₀).hom.app W.obj := by
    rw [hb]
    exact hc
  have hg := etaleCongr_eq A (Category.comp_id q).symm
  have hv : (Etale.affineTraceUnboundedCompactComparison A Y 1).hom.app W.obj =
      (Etale.rightDerivedLowerShriekIso A c₁).hom.app W.obj ≫
      (Etale.rightDerivedLowerShriekCongr A (Category.comp_id q).symm).hom.app W.obj := by
    rw [hg]
    exact hU
  exact finish_transport
    ((Etale.rightDerivedLowerShriekIso A c₀).app W.obj)
    ((Etale.rightDerivedLowerShriekIso A c₁).app W.obj)
    ((Etale.rightDerivedLowerShriekCongr A (Category.comp_id q).symm).app W.obj)
    ((Etale.rightDerivedLowerShriekIso A (compactification Y 1)).app W.obj)
    ((Etale.affineTraceUnboundedCompactComparison A Y 1).app W.obj)
    _ (congrArg (fun z ↦ z.app W.obj) hself) hv hp

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
