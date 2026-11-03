/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerGraphOrdinaryOpenSquares
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore

/-! # Ordinary graph compositor comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace CategoryTheory
private theorem right_changed_uniq_symm
    {C D : Type*} [Category C] [Category D]
    {L P : C ⥤ D} {R S : D ⥤ C} (a : L ⊣ R) (b : P ⊣ S) (q : R ≅ S) :
    ((a.ofNatIsoRight q).leftAdjointUniq b).symm =
      (b.ofNatIsoRight q.symm).leftAdjointUniq a := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).injective
  rw [Iso.symm_hom, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply (cancel_mono (q.inv.app (L.obj M))).1
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (b.ofNatIsoRight q.symm) a M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hh
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id, Iso.symm_hom]
  erw [Category.comp_id]
  exact hh.symm


private def forwardIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ C') (f : D ≌ D') (L : C ⥤ D) (P : C' ⥤ D')
    (c : e.inverse ⋙ L ⋙ f.functor ≅ P) : L ⋙ f.functor ≅ e.functor ⋙ P :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ c

private theorem forward_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ C') (f : D ≌ D') {L : C ⥤ D} {R : D ⥤ C}
    {P : C' ⥤ D'} {S : D' ⥤ C'} (a : L ⊣ R) (b : P ⊣ S)
    (q : f.inverse ⋙ R ⋙ e.functor ≅ S) :
    a.IsMateSquare b
      (forwardIso e f L P
        (((e.symm.toAdjunction.comp a).comp f.toAdjunction).ofNatIsoRight q |>.leftAdjointUniq b))
      (forwardIso f e R S q) := by
  apply Adjunction.IsMateSquare.of_unit
  intro M
  have h := open_unit_coordinates e f a b q.symm M
  dsimp only at h
  rw [← right_changed_uniq_symm
    ((e.symm.toAdjunction.comp a).comp f.toAdjunction) b q] at h
  let c := (((e.symm.toAdjunction.comp a).comp f.toAdjunction).ofNatIsoRight q).leftAdjointUniq b
  have h' : b.unit.app (e.functor.obj M) ≫
      S.map ((forwardIso e f L P c).inv.app M) =
      e.functor.map (a.unit.app M) ≫ (forwardIso f e R S q).hom.app (L.obj M) := by
    simp only [forwardIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
      Equivalence.funInvIdAssoc_inv_app, Equivalence.unit, Functor.comp_map,
      Category.id_comp, Category.comp_id, Category.assoc, c] at h ⊢
    erw [Category.id_comp, Category.comp_id] at h
    erw [Category.comp_id]
    exact h
  have hh := congrArg (fun t ↦ t ≫ S.map ((forwardIso e f L P c).hom.app M)) h'
  simp only [Category.assoc, ← S.map_comp, Iso.inv_hom_id_app] at hh
  erw [S.map_id, Category.comp_id] at hh
  simpa only [Functor.idSquareIso_hom_app, Functor.pasteSquareIso_hom_app,
    Category.id_comp, Category.assoc] using hh.symm

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Compatibility of the open compositor follows from compatibility of inverse images.
Source: Local pairs, adjunction uniqueness; Stacks 03DI and 07A7.
(blueprint: lem-sp-graph-ordinary-open-mate-composition).

Proof: the forward graph open square is inverse-mate to the forward graph pull
square. This follows by expanding the conjugated adjunction, applying the unit
normalization of leftAdjointUniq, then cancelling the presentation unit/counit by
the equivalence triangles. Transport both mate squares along the fixed ordinary
semilinear/varying-ring equalities. Paste the two mate squares. Invert the supplied
pull-compositor equation to obtain compatibility of the right-adjoint compositors.
Apply injectivity of the mate correspondence to that compatibility equation. The
left compositors are the two leftAdjointUniq comparisons defining
graphOrdinaryOpenComp and moduleJComp, so the resulting left square is exactly
the displayed equation. No derived evaluation, faithfulness or resolution is used. -/
theorem graph_ordinary_open_composition_of_pull (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {U X Z : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i]
    (hp : ∀ N : SpTowerShriek.S l E Z,
      (g.presentation U).functor.map ((o.ordinaryComp j i).inv.app N) ≫
          (graphPullSquare l E b o g j).hom.app ((o.geometry i).pull.obj N) ≫
          (VaryingRing.pull (graphRings l E) (graphTransitions l E) j).map
            ((graphPullSquare l E b o g i).hom.app N) =
        (graphPullSquare l E b o g (j ≫ i)).hom.app N ≫
          (VaryingRing.moduleGComp (graphRings l E) (graphTransitions l E) j i).hom.app
            ((g.presentation Z).functor.obj N)) (N : SpTowerShriek.S l E U) :
    (g.presentation Z).functor.map ((graphOrdinaryOpenComp l E b o j i).hom.app N) ≫
        (graphOpenSquare l E b o g (j ≫ i)).hom.app N =
      (graphOpenSquare l E b o g i).hom.app ((o.openOp j).extension.obj N) ≫
        (VaryingRing.extension (graphRings l E) (graphTransitions l E) i).map
          ((graphOpenSquare l E b o g j).hom.app N) ≫
        (VaryingRing.moduleJComp (graphRings l E) (graphTransitions l E) j i).hom.app
          ((g.presentation U).functor.obj N) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
