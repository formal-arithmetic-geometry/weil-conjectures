/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TransportIntegralCounitData
import WeilConjectures.AlgebraicGeometry.SpecifiedTowerAdjunctionCharts

/-! # Charts of the transported integral adjunction

Source: purity-transport, the existing integral realization argument.
(blueprint: lem-pur-integral-chart-realization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

-- Keep the canonical small-site sheafification instance ahead of generic alternatives.
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private theorem chart_counit_transport
    {C D B : Type*} [Category C] [Category D] [Category B]
    (F : C ⥤ B) (L : D ⥤ C) (U : C ⥤ D) (a : L ⊣ U)
    (H : D ⥤ B) (c : L ⋙ F ≅ H) {J G : C} {Q : D}
    (g : J ≅ G) (q : U.obj G ≅ Q) {K : B} (eps : F.obj G ⟶ K) :
    H.map (q.inv ≫ U.map g.inv) ≫ c.inv.app (U.obj J) ≫
        F.map (a.counit.app J) ≫ F.map g.hom ≫ eps =
      H.map q.inv ≫ c.inv.app (U.obj G) ≫ F.map (a.counit.app G) ≫ eps := by
  rw [H.map_comp, Category.assoc, c.inv.naturality_assoc]
  simp only [Functor.comp_map]
  have hn : L.map (U.map g.inv) ≫ a.counit.app J = a.counit.app G ≫ g.inv :=
    a.counit.naturality g.inv
  rw [← F.map_comp_assoc, hn, F.map_comp]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc g.inv g.hom, g.inv_hom_id, F.map_id, Category.id_comp]

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit

variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [QuasiSeparatedSpace Y]

/-- The transported tower adjunction has the precise fibre-sum and ordered
projective-line integration counits on every affine chart. The comparison to the
exceptional tower has the actual gamma components, including its diagonal orientation.
Source: purity-transport Step 2, final paragraph; tower-gluing clauses (1)--(2).
(blueprint: lem-pur-integral-chart-realization).

Proof: specified_tower_adjunction_charts retains the normalized chart pairs and their
explicit counit equations for m.exceptional and m.adjunction at the fixed
compactification. The recorded purity naturality assembles the actual gamma into a
natural transformation. Whisker it by the inverse coordinate realization and compose
with that equivalence's inverse unit. Full-subcategory faithfulness and the recorded
invertibility give the displayed isomorphism g, with exactly the stated components.
Pull g back to each open chart and compose with the original chart comparison.
Naturality of openComposition and the open adjunction counit moves the inverse of g
through the chart counit word. It cancels g from the transported global counit,
leaving the original chart counit equation. The normalized chart pairs, including the
zero-dimensional identity integration and empty charts, are retained verbatim. -/
theorem chart_realization (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d)
    [IsNoetherian X] [IsNoetherian Y]
    [SmoothOfRelativeDimension d (j ≫ p)] :
    ∃ g : towerSource P D j p d E m ≅ m.exceptional,
      (∀ K : SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) Y,
        (g.hom.app K).hom =
          (SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
            ((D.coordinates E).abelian X)).inverse.map
              (SpTowerGamma.gamma P.coefficients.l E.val (D.base E) (D.operations E)
                (D.coordinates E) (SpTowerGamma.factorization j p) m.twists d
                m.realization.purity.tensorX m.realization.purity.tensorY
                m.supportClosed m.exceptional m.adjunction m.realization.purity.unit_mem
                m.realization.purity.orientation K (m.realization.purity.tensor_mem K)
                (m.realization.purity.projection_iso K)) ≫
            (SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
              ((D.coordinates E).abelian X)).unitIso.inv.app (m.exceptional.obj K).obj) ∧
      Nonempty (SpTowerGluing.Charts P.coefficients.l E.val (D.base E) (D.operations E)
        (D.coordinates E) P.field.k (X.asOver (Spec (.of P.field.k)))
        (Y.asOver (Spec (.of P.field.k)))
        ⟨‹IsSeparated (Y ↘ Spec (.of P.field.k))›,
          ‹LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))›,
          ‹QuasiCompact (Y ↘ Spec (.of P.field.k))›⟩
        ((j ≫ p).asOver (Spec (.of P.field.k))) d (SpTowerGamma.factorization j p)
        m.supportClosed (towerSource P D j p d E m)
        (m.adjunction.ofNatIsoRight g.symm)) := by
  let ex := SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
    ((D.coordinates E).abelian X)
  let i := (spConstructibleTorTowers P.coefficients.l E.val X
    ((D.coordinates E).abelian X)).ι
  let G := m.exceptional ⋙ i
  let gamma : SpTowerGamma.source P.coefficients.l E.val (D.base E) (D.operations E)
        (D.coordinates E) (j ≫ p) m.twists d ⟶
      SpTowerGamma.exceptional P.coefficients.l E.val (D.base E)
        (D.coordinates E) m.exceptional :=
    { app K := SpTowerGamma.gamma P.coefficients.l E.val (D.base E) (D.operations E)
        (D.coordinates E) (SpTowerGamma.factorization j p) m.twists d
        m.realization.purity.tensorX m.realization.purity.tensorY m.supportClosed
        m.exceptional m.adjunction m.realization.purity.unit_mem
        m.realization.purity.orientation K
        (m.realization.purity.tensor_mem K) (m.realization.purity.projection_iso K)
      naturality K L v := m.realization.purity.naturality K L v }
  let t : towerSource P D j p d E m ⋙ i ⟶ m.exceptional ⋙ i :=
    Functor.whiskerRight gamma ex.inverse ≫ Functor.whiskerLeft G ex.unitIso.inv
  let z : towerSource P D j p d E m ⟶ m.exceptional :=
    { app K := ObjectProperty.homMk (t.app K)
      naturality K L v := by
        apply ObjectProperty.hom_ext
        exact t.naturality v }
  have hz (K : SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) Y) :
      IsIso (z.app K) := by
    have : IsIso (gamma.app K) := m.realization.purity.purity_iso K
    have : IsIso (i.map (z.app K)) := by
      change IsIso (ex.inverse.map (gamma.app K) ≫ ex.unitIso.inv.app (G.obj K))
      infer_instance
    exact isIso_of_reflects_iso _ i
  let g : towerSource P D j p d E m ≅ m.exceptional :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (z.app K) (hz K))
      (fun v ↦ z.naturality v)
  obtain ⟨B⟩ := specified_tower_adjunction_charts P D j p d E m
  let B' : SpTowerGluing.Charts P.coefficients.l E.val (D.base E) (D.operations E)
      (D.coordinates E) P.field.k (X.asOver (Spec (.of P.field.k)))
      (Y.asOver (Spec (.of P.field.k)))
      ⟨‹IsSeparated (Y ↘ Spec (.of P.field.k))›,
        ‹LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))›,
        ‹QuasiCompact (Y ↘ Spec (.of P.field.k))›⟩
      ((j ≫ p).asOver (Spec (.of P.field.k))) d (SpTowerGamma.factorization j p)
      m.supportClosed (towerSource P D j p d E m)
      (m.adjunction.ofNatIsoRight g.symm) :=
    { finiteCoordinates := B.finiteCoordinates
      preservation := B.preservation
      calculus := B.calculus
      etale_normalized := B.etale_normalized
      etale_refinement := B.etale_refinement
      twists := B.twists
      chart := B.chart
      normalized := B.normalized
      open_properties := B.open_properties
      comparison K U e _ _ _ _ he :=
        (SpTowerCalculus.etalePullback P.coefficients.l E.val (D.base E) (D.operations E)
          (D.coordinates E) U.ι).mapIso (i.mapIso (g.app K)) ≪≫ B.comparison K U e he
      counit K U e _ _ _ _ he ho := by
        simpa only [Iso.trans_inv, Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp,
          Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
          Iso.symm_inv, ObjectProperty.FullSubcategory.comp_hom, SpTowerGluing.support,
          ObjectProperty.lift_map, ObjectProperty.homMk_hom, Functor.comp_map,
          i, ObjectProperty.ι_obj, ObjectProperty.ι_map, Iso.app_hom, Iso.app_inv,
          Category.assoc] using
          (chart_counit_transport
            (SpTowerCalculus.F P.coefficients.l E.val (D.base E) (D.operations E)
              (D.coordinates E) (SpTowerGamma.factorization j p))
            _ _ (SpTowerGluing.openAdjunction P.coefficients.l E.val (D.base E)
              (D.operations E) (D.coordinates E) U.ι) _
            (SpTowerCalculus.openComposition P.coefficients.l E.val (D.base E)
              (D.operations E) (D.coordinates E) U.ι (SpTowerGamma.factorization j p))
            (i.mapIso (g.app K)) (B.comparison K U e he) (m.adjunction.counit.app K).hom).trans
              (B.counit K U e he ho) }
  exact ⟨g, fun _ ↦ rfl, ⟨B'⟩⟩


end AlgebraicGeometry.ProEtale.TransportIntegralCounit
