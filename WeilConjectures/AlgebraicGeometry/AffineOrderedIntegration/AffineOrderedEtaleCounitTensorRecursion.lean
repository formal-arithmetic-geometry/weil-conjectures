/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedSupportedTensorCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEtaleSourceReassociation
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEtaleCounitSiteTransport
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedOrdinaryCounitStep

/-! # Pasting site transport and ordinary tensor recursion

Source: projection-purity agreement, final canonical-reassociation paragraph.
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
attribute [local implicit_reducible] sourceWitness

private theorem iso_coordinates_factor
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W : D} {X Y Z : C} (a : W ≅ F.obj X) (b : X ≅ Y) (c : Y ≅ Z) :
    (a ≪≫ F.mapIso (b ≪≫ c)).hom =
      (a ≪≫ F.mapIso b).hom ≫ F.map c.hom := by
  dsimp only [Iso.trans, Functor.mapIso]
  rw [F.map_comp]
  exact (Category.assoc _ _ _).symm

private theorem counit_coordinates_paste
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B V W : D} {X Y X' Y' : C}
    (a : A ⟶ B) (b : B ⟶ V) (c : V ⟶ W) (s : W ⟶ F.obj X)
    (t : A ⟶ F.obj Y) (o : Y ⟶ X) (e : X ⟶ X') (e' : Y ⟶ Y')
    (q : Y' ⟶ X')
    (hs : a ≫ b ≫ c ≫ s = t ≫ F.map o) (ho : o ≫ e = e' ≫ q) :
    a ≫ b ≫ c ≫ (s ≫ F.map e) = (t ≫ F.map e') ≫ F.map q := by
  have hsp := congrArg (fun z ↦ z ≫ F.map e) hs
  have hop := congrArg (fun z ↦ t ≫ F.map z) ho
  simp only [Functor.map_comp, Category.assoc] at hsp hop ⊢
  exact hsp.trans hop

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
-- Instantiating the pasting lemmas elaborates the full derived support-coordinate types.
/-- Successor tensor/support recursion after the line realization has been cancelled.
Source: projection-purity agreement, final canonical-reassociation paragraph.
(blueprint: lem-pur-affine-ordered-etale-counit-tensor-recursion).
Proof: postcompose etaleCounit_site_transport with comparison of the preceding
ordinary tensor coordinates. Apply comparison to ordinaryEtaleCounitStep_coordinates
and precompose with the successor site-support coordinates. The intermediate maps
coincide by functoriality. Transitivity and expansion of supportedTensorCoordinates
prove the equality. -/
theorem etaleCounit_tensor_recursion
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ)
    (H : Plus (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1)))
    (hJ : etaleFiniteTor (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))
      (sourceEtale P Y Ke (d + 1)))
    (eH : (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))).obj
      (sourceEtale P Y Ke (d + 1)) ≅ H.obj)
    (hJnext : DerivedCategory.TStructure.t.plus (sourceEtale P Y Ke (d + 2))) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
    letI : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
    letI : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
    letI : IsNoetherian (iteratedAffineLine Y (d + 1)) :=
      tower_noetherian P Y aY (d + 1)
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 2))).map
      ((comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 2))).map
          (etaleSourceReassociation P Y aY Ke d).hom ≫
        (AffineLineEvaluation.lineWitness P (iteratedAffineLine Y (d + 1)) H.obj
          (sourceEtale P Y Ke (d + 1)) hJ eH).iso.hom) ≫
    (AffineLineEvaluation.compositor P aY (iteratedAffineLineProj Y (d + 1))
      H.obj (sourceEtale P Y Ke (d + 1)) hJ eH).inv ≫
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
      ((lineEvaluationCoordinates P (iteratedAffineLine Y (d + 1))
        (towerBase aY (d + 1)) H (sourceEtale P Y Ke (d + 1)) hJ eH).hom ≫
      (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))).map
        (orderedCounitStep P (iteratedAffineLine Y (d + 1))
          (towerBase aY (d + 1)) (sourceEtale P Y Ke (d + 1)) 0)) ≫
    (supportedTensorCoordinates P Y aY Ke hKe (d + 1) hJ.1.1.1).hom =
      (supportedTensorCoordinates P Y aY Ke hKe (d + 2) hJnext).hom ≫
        (comparison (AffineLinePurity.Ring P) Y).map
          (orderedCounitStep P Y aY Ke (d + 1)) := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
  let : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
  let : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
  let : IsNoetherian (iteratedAffineLine Y (d + 1)) :=
    tower_noetherian P Y aY (d + 1)
  have hc (n : ℕ) (hn : DerivedCategory.TStructure.t.plus (sourceEtale P Y Ke n)) :
      (supportedTensorCoordinates P Y aY Ke hKe n hn).hom =
        (ordinarySupportCoordinates P Y Ke n hn).hom ≫
          (comparison (AffineLinePurity.Ring P) Y).map
            (ordinaryTensorCoordinates P Y aY Ke hKe n).hom := by
    let := (projection_geometry Y n).2
    dsimp only [supportedTensorCoordinates, ordinarySupportCoordinates]
    exact iso_coordinates_factor (comparison (AffineLinePurity.Ring P) Y)
      ((compactSupportSiteComparison (AffineLinePurity.Ring P)
        (compactification Y n)).app ⟨_, hn⟩)
      ((Etale.rightDerivedLowerShriekIso (AffineLinePurity.Ring P)
        (compactification Y n)).app (sourceEtale P Y Ke n))
      (ordinaryTensorCoordinates P Y aY Ke hKe n)
  rw [hc (d + 1) hJ.1.1.1, hc (d + 2) hJnext]
  exact counit_coordinates_paste (comparison (AffineLinePurity.Ring P) Y)
    _ _ _ _ _ _ _ _ _
    (etaleCounit_site_transport P Y aY Ke d H hJ eH hJnext)
    (ordinaryEtaleCounitStep_coordinates P Y aY Ke hKe d)

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
