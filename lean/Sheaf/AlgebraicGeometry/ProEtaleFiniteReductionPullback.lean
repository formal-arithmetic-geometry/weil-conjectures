/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E6
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Topology.Category.Profinite.Limits

/-!
# Base change for one normalized finite reduction

The finite constant-sheaf identifications and the adjunction-mate calculation for a
single continuous finite quotient. This calculation is independent of the integral
limit and of its ring-compatible comparison.

Source: blueprint main-20261015, coefficient pullback proof, second paragraph
(blueprint: lem-sfb-finite-reduction-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison between a constant commutative ring sheaf, regarded as
an abelian sheaf, and the constant abelian sheaf of its additive group.
Source: blueprint pullback clause 1, canonical finite constant-sheaf identifications
(blueprint: det-prop-sfb-qlbar-colimit-x-pullback). -/
def sfbConstantRingAbIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)) ≅
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of A) :=
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app A) ≪≫
    (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).app ((forget₂ CommRingCat RingCat).obj A)

/-- The canonical finite constant coefficient comparison, with the ring-sheaf encoding
transported to abelian sheaves by the canonical constant/forgetful comparison.
Source: blueprint pullback clause 1, the constant-sheaf identifications
(blueprint: det-prop-sfb-qlbar-colimit-x-pullback). -/
def sfbFiniteCoefficientPullbackIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (f)^*[Ab.{u + 1}].obj
        ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (integralCoefficientSheaf l E Y n)) ≅
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (integralCoefficientSheaf l E X n) :=
  (f)^*[Ab.{u + 1}].mapIso
    (sfbConstantRingAbIso Y
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    (constantSheafCompUpperStarIso Ab.{u + 1} f).app
      (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ≪≫
    (sfbConstantRingAbIso X
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).symm

private theorem homEquiv_rightUniq
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L ⊣ R') {M : C} {N : D} (t : L.obj M ⟶ N) :
    a.homEquiv _ _ t ≫ (a.rightAdjointUniq b).hom.app N = b.homEquiv _ _ t := by
  simp only [Adjunction.homEquiv_unit, Category.assoc]
  rw [(a.rightAdjointUniq b).hom.naturality,
    a.unit_rightAdjointUniq_hom_app_assoc b]

private theorem constantGamma_homEquiv {C : Type*} [Category* C] [HasTerminal C]
    (J : GrothendieckTopology C) (D : Type*) [Category* D] [HasWeakSheafify J D]
    {T : C} (hT : IsTerminal T) (A : D) (F : Sheaf J D)
    (t : (constantSheaf J D).obj A ⟶ F) :
    (constantSheafΓAdj J D).homEquiv A F t ≫
        (Sheaf.ΓNatIsoSheafSections J D hT).hom.app F =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op T) ≫ t.hom.app (op T) := by
  rw [Sheaf.ΓNatIsoSheafSections, homEquiv_rightUniq,
    constantSheafAdj, Adjunction.comp_homEquiv]
  change 𝟙 A ≫ _ = _
  rw [Category.id_comp]
  rfl

private theorem constantGamma_unit {C : Type*} [Category* C] [HasTerminal C]
    (J : GrothendieckTopology C) (D : Type*) [Category* D] [HasWeakSheafify J D]
    {T : C} (hT : IsTerminal T) (A : D) :
    (constantSheafΓAdj J D).unit.app A ≫
        (Sheaf.ΓNatIsoSheafSections J D hT).hom.app ((constantSheaf J D).obj A) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op T) := by
  rw [Sheaf.ΓNatIsoSheafSections, Adjunction.unit_rightAdjointUniq_hom_app,
    constantSheafAdj, Adjunction.comp_unit_app]
  change 𝟙 A ≫ _ = _
  rw [Category.id_comp]
  rfl

private theorem compLeftUniq_unit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {N : E ⥤ D}
    {K : C ⥤ E} {S : E ⥤ C}
    (a : L ⊣ R) (b : M ⊣ N) (c : K ⊣ S) (e : N ⋙ R ≅ S) (A : C) :
    a.homEquiv _ _ (b.homEquiv _ _
        ((((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app A)) ≫
      e.hom.app (K.obj A) = c.unit.app A := by
  have h := ((a.comp b).ofNatIsoRight e).homEquiv_leftAdjointUniq_hom_app c A
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  exact h

attribute [local irreducible] upperStarLowerStarAdjunction constantSheafΓAdj
  globalSectionsLowerStarIso

private theorem constantPullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Ab.{u + 1}) (V : Y.ProEtᵒᵖ) :
    (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app V ≫
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _)
        ((constantSheafCompUpperStarIso Ab.{u + 1} f).hom.app A)).hom.app V =
    (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V.unop)) := by
  have h := compLeftUniq_unit
    (constantSheafΓAdj (Scheme.ProEt.topology Y) Ab.{u + 1})
    (upperStarLowerStarAdjunction Ab.{u + 1} f)
    (constantSheafΓAdj (Scheme.ProEt.topology X) Ab.{u + 1})
    (globalSectionsLowerStarIso Ab.{u + 1} f) A
  change (constantSheafΓAdj (Scheme.ProEt.topology Y) Ab.{u + 1}).homEquiv _ _
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _)
        ((constantSheafCompUpperStarIso Ab.{u + 1} f).hom.app A)) ≫
      (globalSectionsLowerStarIso Ab.{u + 1} f).hom.app _ =
        (constantSheafΓAdj (Scheme.ProEt.topology X) Ab.{u + 1}).unit.app A at h
  have hh := congrArg (fun t ↦ t ≫
    (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) Ab.{u + 1}
      (Scheme.ProEt.isTerminalMkId X)).hom.app _) h
  simp only [globalSectionsLowerStarIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] at hh
  rw [← Category.assoc, constantGamma_homEquiv, constantGamma_unit] at hh
  dsimp only [NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp] at hh
  simp only [Category.id_comp] at hh
  let F := (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj A
  let B := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let e := overPullbackObjMkIdIso f
  dsimp only [Functor.mapIso, Iso.op, sheafSections] at hh
  change _ ≫ F.obj.map e.inv.op = _ at hh
  have ht := congrArg (fun t ↦ t ≫ F.obj.map e.hom.op) hh
  rw [Category.assoc, ← F.obj.map_comp, ← op_comp, e.hom_inv_id,
    op_id, F.obj.map_id, Category.comp_id] at ht
  have hu := (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj A)).naturality e.hom.op
  change 𝟙 A ≫ _ = _ ≫ F.obj.map e.hom.op at hu
  rw [Category.id_comp] at hu
  have ht' := ht.trans hu.symm
  let v := (Scheme.ProEt.isTerminalMkId Y).from V.unop
  let t := ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _)
    ((constantSheafCompUpperStarIso Ab.{u + 1} f).hom.app A)
  have hn := (toSheafify (Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj A) ≫ t.hom).naturality v.op
  simp only [Functor.const_obj_map, NatTrans.comp_app] at hn
  change 𝟙 A ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  change _ = _ ≫ F.obj.map (B.map v).op at hn
  rw [ht'] at hn
  have hx := (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj A)).naturality (B.map v).op
  change 𝟙 A ≫ _ = _ at hx
  rw [Category.id_comp] at hx
  exact hn.trans hx.symm

private abbrev finitePoint : FintypeCat.{u} := FintypeCat.of PUnit.{u + 1}

private noncomputable def finiteLabel (R : FintypeCat.{u}) (r : R) : finitePoint ⟶ R :=
  FintypeCat.homMk (fun _ ↦ r)

private noncomputable def finitePointTerminal (X : Scheme.{u}) :
    IsTerminal ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj finitePoint)) := by
  have : PreservesFiniteLimits (profiniteToProEtOf X) := by
    have : PreservesFiniteLimits profiniteToProEt.{u} := inferInstance
    have : PreservesFiniteLimits
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) := inferInstance
    exact comp_preservesFiniteLimits _ _
  exact Profinite.isTerminalPUnit.isTerminalObj (profiniteToProEtOf X) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteRepresentation_constant (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : FintypeCat.{u}) (r : R) (V : X.ProEtᵒᵖ) :
    (a.hom.app R).app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1} R))).app V (ULift.up r)) =
      ULift.up ((finitePointTerminal X).from V.unop ≫
        (profiniteToProEtOf X).map (FintypeCat.toProfinite.map (finiteLabel R r))) := by
  have hn := congrArg (fun t ↦ t.app V
    ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1} PUnit.{u + 1}))).app V
        (ULift.up PUnit.unit))) (a.hom.naturality (finiteLabel R r))
  have hu := congrArg (fun t ↦ t.app V (ULift.up PUnit.unit))
    (toSheafify_naturality (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map
        (uliftFunctor.{u + 1}.map ((forget FintypeCat).map (finiteLabel R r)))))
  change (a.hom.app R).app V _ = ULift.up
    (((a.hom.app finitePoint).app V _).down ≫
      (profiniteToProEtOf X).map (FintypeCat.toProfinite.map (finiteLabel R r))) at hn
  change (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1} R))).app V (ULift.up r) =
    ((sfbFiniteConstantSets X).map (finiteLabel R r)).app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1} PUnit.{u + 1}))).app V
          (ULift.up PUnit.unit)) at hu
  have hh := (congrArg (fun z ↦ (a.hom.app R).app V z) hu).trans hn
  exact hh.trans (congrArg (fun t ↦ ULift.up (t ≫
    (profiniteToProEtOf X).map (FintypeCat.toProfinite.map (finiteLabel R r))))
      ((finitePointTerminal X).hom_ext _ _))

private noncomputable def testBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    profiniteToProEtOf Y ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ f ≅
      profiniteToProEtOf X :=
  NatIso.ofComponents
    (fun S ↦ ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
      f (toSpecZ Y)).symm ≪≫
        MorphismProperty.Over.pullbackCongr (comp_toSpecZ f)).app (profiniteToProEt.obj S))
    (by
      intro S T g
      exact ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
        f (toSpecZ Y)).symm ≪≫
          MorphismProperty.Over.pullbackCongr (comp_toSpecZ f)).hom.naturality
            (profiniteToProEt.map g))

private theorem testBaseChange_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Profinite.{u}) :
    (testBaseChange f).hom.app S =
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
        f (toSpecZ Y)).inv.app (profiniteToProEt.obj S) ≫
        (MorphismProperty.Over.pullbackCongr (comp_toSpecZ f)).hom.app
          (profiniteToProEt.obj S) := rfl

private theorem lowerStar_eqToHom_app {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (V : Y.ProEtᵒᵖ) :
    ((eqToHom (congrArg (lowerStar Ab.{u + 1}) h.symm)).app F).hom.app V =
      F.obj.map ((MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤)
        h).hom.app V.unop).op := by
  subst h
  simp only [eqToHom_refl, NatTrans.id_app, MorphismProperty.Over.pullbackCongr_refl,
    Iso.refl_hom, op_id, NatTrans.id_app]
  rw [F.obj.map_id]
  rfl

private theorem lowerStarTransport_app {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kX : X ⟶ W) (kY : Y ⟶ W) (h : f ≫ kY = kX)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (V : W.ProEtᵒᵖ) :
    ((eqToHom (congrArg (lowerStar Ab.{u + 1}) h.symm)).app F ≫
      (lowerStarComp Ab.{u + 1} f kY).inv.app F).hom.app V =
      F.obj.map (((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
        f kY).inv.app V.unop ≫
          (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤)
            h).hom.app V.unop).op) := by
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_eqToHom_app h, lowerStarComp_inv_app_hom_app]
  rw [op_comp, F.obj.map_comp]

@[irreducible]
private noncomputable def directImageTransport {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kX : X ⟶ W) (kY : Y ⟶ W) (h : f ≫ kY = kX) :
    (kX)_*[Ab.{u + 1}] ≅ (f)_*[Ab.{u + 1}] ⋙ (kY)_*[Ab.{u + 1}] :=
  eqToIso (congrArg (lowerStar Ab.{u + 1}) h.symm) ≪≫
    (lowerStarComp Ab.{u + 1} f kY).symm

private theorem directImageTransport_app {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kX : X ⟶ W) (kY : Y ⟶ W) (h : f ≫ kY = kX)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (directImageTransport f kX kY h).hom.app F =
      (eqToHom (congrArg (lowerStar Ab.{u + 1}) h.symm)).app F ≫
        (lowerStarComp Ab.{u + 1} f kY).inv.app F := by
  unfold directImageTransport
  rfl

private theorem pointLowerStar_map_app
    {F G : Sheaf (Scheme.ProEt.topology specZ.{u}) Ab.{u + 1}}
    (t : F ⟶ G) (S : Profinite.{u}) :
    (pointLowerStar.map t).hom.app (op S) = t.hom.app (op (profiniteToProEt.obj S)) := rfl

private theorem pointAdj_map_app (X : Scheme.{u})
    {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (t : F ⟶ G)
    (S : Profinite.{u}) :
    ((sfbPullbackFromPointRightAdjoint X).map t).hom.app (op S) =
      t.hom.app (op ((profiniteToProEtOf X).obj S)) := rfl

private theorem precomposeEq {C : Type*} [Category* C] {W X Y : C}
    (u : W ⟶ X) {f g : X ⟶ Y} (h : f = g) : u ≫ f = u ≫ g :=
  congrArg (fun z ↦ u ≫ z) h

attribute [local irreducible] pointUpperStarLowerStarAdjunction

private theorem pointAdj_eq (X : Scheme.{u}) :
    sfbIntegralPointAdjunction X = pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)) := rfl

private theorem pointComp_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStarFromPointComp f =
      Functor.associator pointUpperStar (toSpecZ Y)^*[Ab.{u + 1}] (f)^*[Ab.{u + 1}] ≪≫
        Functor.isoWhiskerLeft pointUpperStar
          ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).symm ≪≫
            eqToIso (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f))) := rfl

/-- Lift compositor coherence through a preceding adjunction before taking components. -/
private theorem unit_comparison_natural {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    {G : C ⥤ D} {R : D ⥤ C} {LY : D ⥤ E} {RY : E ⥤ D}
    {LF : E ⥤ F} {RF : F ⥤ E} {LX : D ⥤ F} {RX : F ⥤ D}
    (P : G ⊣ R) (aY : LY ⊣ RY) (aF : LF ⊣ RF) (aX : LX ⊣ RX)
    (α : LY ⋙ LF ⟶ LX) (β : RX ⟶ RF ⋙ RY)
    (h : ∀ B : D, aY.unit.app B ≫
      RY.map (aF.unit.app (LY.obj B) ≫ RF.map (α.app B)) =
        aX.unit.app B ≫ β.app (LX.obj B)) :
    ((P.comp aY).comp aF).unit ≫
      Functor.whiskerRight
        ((Functor.associator G LY LF).hom ≫ Functor.whiskerLeft G α)
        (RF ⋙ (RY ⋙ R)) =
      (P.comp aX).unit ≫ Functor.whiskerLeft (G ⋙ LX)
        (Functor.whiskerRight β R ≫ (Functor.associator RF RY R).hom) := by
  apply NatTrans.ext
  funext A
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id,
    Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map, Category.assoc]
  have hr := congrArg (fun z ↦ P.unit.app A ≫ R.map z) (h (G.obj A))
  simpa only [Functor.map_comp, Category.assoc] using hr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem point_comparison_natural {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((sfbIntegralPointAdjunction Y).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f)).unit ≫
      Functor.whiskerRight (upperStarFromPointComp f).hom
        ((f)_*[Ab.{u + 1}] ⋙ sfbPullbackFromPointRightAdjoint Y) =
      (sfbIntegralPointAdjunction X).unit ≫
        Functor.whiskerLeft (upperStarFromPoint X)
          (Functor.whiskerRight (directImageTransport f (toSpecZ X) (toSpecZ Y)
            (comp_toSpecZ f)).hom pointLowerStar ≫
            (Functor.associator (f)_*[Ab.{u + 1}] (toSpecZ Y)_*[Ab.{u + 1}]
              pointLowerStar).hom) := by
  rw [pointAdj_eq, pointAdj_eq, pointComp_eq, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  exact unit_comparison_natural pointUpperStarLowerStarAdjunction
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))
    (upperStarLowerStarAdjunction Ab.{u + 1} f)
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
    ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).inv ≫
      eqToHom (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f)))
    (directImageTransport f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)).hom
    (by
      intro B
      rw [NatTrans.comp_app, directImageTransport_app]
      exact unit_comp_lowerStar_map_unit_comp_upperStarComp Ab.{u + 1}
        f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem point_comparison_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    ((sfbIntegralPointAdjunction Y).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f)).unit.app A ≫
        ((f)_*[Ab.{u + 1}] ⋙ sfbPullbackFromPointRightAdjoint Y).map
          ((upperStarFromPointComp f).hom.app A) =
      (sfbIntegralPointAdjunction X).unit.app A ≫ pointLowerStar.map
        ((directImageTransport f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)).hom.app
          ((upperStarFromPoint X).obj A)) := by
  have h := congrArg (fun t ↦ t.app A) (point_comparison_natural f)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] using h

private theorem point_transport_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (r : A ⟶ ((f)_*[Ab.{u + 1}] ⋙ sfbPullbackFromPointRightAdjoint Y).obj F)
    (v : A ⟶ (sfbPullbackFromPointRightAdjoint X).obj F)
    (h : r = v ≫ pointLowerStar.map
      ((directImageTransport f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)).hom.app F))
    (S : Profinite.{u}) :
    r.hom.app (op S) = v.hom.app (op S) ≫
      F.obj.map ((testBaseChange f).hom.app S).op := by
  have hs := congrArg (fun z ↦ z.hom.app (op S)) h
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    pointLowerStar_map_app, directImageTransport_app,
    lowerStarTransport_app f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) F
      (op (profiniteToProEt.obj S))] at hs
  rw [testBaseChange_hom_app]
  exact hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem point_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (S : Profinite.{u}) :
    (((sfbIntegralPointAdjunction Y).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f)).homEquiv _ _
        ((upperStarFromPointComp f).hom.app A)).hom.app (op S) =
      ((sfbIntegralPointAdjunction X).unit.app A).hom.app (op S) ≫
        ((upperStarFromPoint X).obj A).obj.map ((testBaseChange f).hom.app S).op := by
  rw [Adjunction.homEquiv_unit]
  exact point_transport_app f A ((upperStarFromPoint X).obj A) _ _
    (point_comparison_unit f A) S

set_option backward.isDefEq.respectTransparency false in
private theorem constantCommute_unit {C D B : Type*} [Category* C] [Category* D]
    [Category* B] (J : GrothendieckTopology C) (U : D ⥤ B)
    [HasWeakSheafify J D] [HasWeakSheafify J B]
    [J.HasSheafCompose U] [J.PreservesSheafification U] (A : D) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) U ≫
        ((constantCommuteCompose J U).hom.app A).hom =
      (Functor.constComp Cᵒᵖ A U).hom ≫
        toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac, ← toSheafify_naturality]

private noncomputable abbrev finiteAbSheaf (X : Scheme.{u}) (R : Type u) [CommRing R] :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} R))))

private noncomputable def finiteMate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type u) [CommRing R] : finiteAbSheaf Y R ⟶ (f)_*[Ab.{u + 1}].obj
      (finiteAbSheaf X R) :=
  (sfbConstantRingAbIso Y (CommRingCat.of (ULift.{u + 1} R))).hom ≫
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
      ((constantSheafCompUpperStarIso Ab.{u + 1} f).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} R))) ≫
      (f)_*[Ab.{u + 1}].map
        (sfbConstantRingAbIso X (CommRingCat.of (ULift.{u + 1} R))).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantRingAb_unit (X : Scheme.{u}) (A : CommRingCat.{u + 1})
    (V : X.ProEtᵒᵖ) (x : A) :
    (sfbConstantRingAbIso X A).hom.hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj A)).app V x) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V x := by
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have h₁ := congrArg (fun t ↦ t.app V x)
    (constantCommute_unit (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) A)
  have h₂ := congrArg (fun t ↦ t.app V x)
    (constantCommute_unit (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A))
  exact (congrArg (fun z ↦ ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).hom.app
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A)).hom.app V z) h₁).trans h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteMate_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type u) [CommRing R] (V : Y.ProEtᵒᵖ) (r : ULift.{u + 1} R) :
    (finiteMate f R).hom.app V
        ((toSheafify (Scheme.ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app V r) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V.unop)) r := by
  let W := op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V.unop)
  let A := CommRingCat.of (ULift.{u + 1} R)
  let c := (sfbConstantRingAbIso X A)
  apply (ConcreteCategory.bijective_of_isIso (c.hom.hom.app W)).injective
  have h := congrArg (fun t ↦ t r) (constantPullback_unit f (AddCommGrpCat.of A) V)
  dsimp only [finiteMate, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app']
  simp only [ConcreteCategory.comp_apply]
  rw [constantRingAb_unit]
  change c.hom.hom.app W (c.inv.hom.app W _) = c.hom.hom.app W _
  rw [show ∀ z, c.hom.hom.app W (c.inv.hom.app W z) = z from fun z ↦
    ConcreteCategory.congr_hom (congr_app (congrArg (fun t ↦ t.hom) c.inv_hom_id) W) z]
  exact h.trans (constantRingAb_unit X A W r).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def finiteRepresentation (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] :
    (finiteAbSheaf X R).obj ⋙ forget Ab.{u + 1} ≅
      uliftYoneda.{u + 1}.obj
        ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj (FintypeCat.of R))) :=
  (sheafToPresheaf _ _).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} R))) ≪≫ a.app (FintypeCat.of R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteRepresentation_unit (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] (V : X.ProEtᵒᵖ) (r : ULift.{u + 1} R) :
    (finiteRepresentation X a R).hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app V r) =
      ULift.up ((finitePointTerminal X).from V.unop ≫
        (profiniteToProEtOf X).map
          (FintypeCat.toProfinite.map (finiteLabel (FintypeCat.of R) r.down))) := by
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget CommRingCat.{u + 1}) := GrothendieckTopology.instPreservesSheafification _ _
  have h := congrArg (fun t ↦ t.app V r)
    (constantCommute_unit (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})
      (CommRingCat.of (ULift.{u + 1} R)))
  change (a.hom.app (FintypeCat.of R)).app V _ = _
  change ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget CommRingCat.{u + 1})).hom.app (CommRingCat.of (ULift.{u + 1} R))).hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app V r) =
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1} R))).app V r at h
  exact (congrArg (fun z ↦ (a.hom.app (FintypeCat.of R)).app V z) h).trans
    (finiteRepresentation_constant X a (FintypeCat.of R) r.down V)

private noncomputable def baseChangeLabels {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : FintypeCat.{u}) :
    uliftYoneda.{u + 1}.obj ((profiniteToProEtOf Y).obj (FintypeCat.toProfinite.obj R)) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op ⋙
        uliftYoneda.{u + 1}.obj
          ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj R)) where
  app V := ↾fun h ↦ ULift.up
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map h.down ≫
      (testBaseChange f).hom.app (FintypeCat.toProfinite.obj R))
  naturality := by
    intro V W g
    ext h
    apply ULift.ext
    change (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
        (g.unop ≫ h.down) ≫ _ =
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map h.down ≫ _)
    rw [Functor.map_comp, Category.assoc]

private theorem locallySurjective_hom_ext {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {P F G : Cᵒᵖ ⥤ Type v}
    (φ : P ⟶ F) [Presheaf.IsLocallySurjective J φ] (hG : Presheaf.IsSheaf J G)
    (a b : F ⟶ G) (h : φ ≫ a = φ ≫ b) : a = b := by
  ext U x
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 hG).isSeparated _
    (Presheaf.imageSieve_mem J φ x)).ext
  rintro V f ⟨y, hy⟩
  have ha := ConcreteCategory.congr_hom (a.naturality f.op) x
  have hb := ConcreteCategory.congr_hom (b.naturality f.op) x
  change a.app (op V) (F.map f.op x) = G.map f.op (a.app U x) at ha
  change b.app (op V) (F.map f.op x) = G.map f.op (b.app U x) at hb
  change G.map f.op (a.app U x) = G.map f.op (b.app U x)
  rw [← ha, ← hb, ← hy]
  exact ConcreteCategory.congr_hom (congr_app h (op V)) y

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteRepresentation_mate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (aY : sfbFiniteConstantSets Y ≅ sfbFiniteRepresentables Y)
    (R : Type u) [CommRing R] [Finite R] :
    Functor.whiskerRight (finiteMate f R).hom (forget Ab.{u + 1}) ≫
        Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
          (finiteRepresentation X aX R).hom =
      (finiteRepresentation Y aY R).hom ≫ baseChangeLabels f (FintypeCat.of R) := by
  let J := Scheme.ProEt.topology Y
  let K := Scheme.ProEt.topology X
  let B := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let A := CommRingCat.of (ULift.{u + 1} R)
  let : J.PreservesSheafification (forget CommRingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let G := (lowerStar (Type (u + 1)) f).obj
    (K.uliftYoneda.{u + 1}.obj
      ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj (FintypeCat.of R))))
  apply locallySurjective_hom_ext J
    (Functor.whiskerRight (toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj A))
      (forget CommRingCat.{u + 1})) G.property
  ext V r
  change (finiteRepresentation X aX R).hom.app (op (B.obj V.unop))
      ((finiteMate f R).hom.app V ((toSheafify J
        ((Functor.const Y.ProEtᵒᵖ).obj A)).app V r)) = _
  rw [finiteMate_unit, finiteRepresentation_unit]
  change _ = ULift.up (B.map
    (((finiteRepresentation Y aY R).hom.app V
      ((toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj A)).app V r)).down) ≫ _)
  rw [finiteRepresentation_unit]
  apply ULift.ext
  rw [B.map_comp, Category.assoc]
  have hn := (testBaseChange f).hom.naturality
    (FintypeCat.toProfinite.map (finiteLabel (FintypeCat.of R) r.down))
  change B.map ((profiniteToProEtOf Y).map _) ≫ _ = _ ≫
    (profiniteToProEtOf X).map _ at hn
  rw [hn, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ (profiniteToProEtOf X).map
    (FintypeCat.toProfinite.map (finiteLabel (FintypeCat.of R) r.down)))
      ((finitePointTerminal X).hom_ext _ _)


private theorem finiteCoefficient_mate (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
        (sfbFiniteCoefficientPullbackIso l E f n).hom =
      finiteMate f (Padic.coefficientExtensionRing l E (n + 1)) := by
  unfold sfbFiniteCoefficientPullbackIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rfl

private theorem compositeMate {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {N : E ⥤ D}
    (a : L ⊣ R) (b : M ⊣ N) {A : C} {B : D} {F : E}
    (r : L.obj A ⟶ B) (t : M.obj B ⟶ F) :
    (a.comp b).homEquiv _ _ (M.map r ≫ t) =
      a.homEquiv _ _ r ≫ R.map (b.homEquiv _ _ t) := by
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ (M.map r ≫ t)) = _
  rw [b.homEquiv_naturality_left, a.homEquiv_naturality_right]

private theorem pullbackSquareOfMates {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {N : E ⥤ D}
    (a : L ⊣ R) (b : M ⊣ N) {A : C} {B : D} {U T : E}
    (r : L.obj A ⟶ B) (c : M.obj B ⟶ T) (α : M.obj (L.obj A) ⟶ U)
    (s : U ⟶ T) (d : B ⟶ N.obj T) (hd : b.homEquiv _ _ c = d)
    (h : a.homEquiv _ _ r ≫ R.map d =
      (a.comp b).homEquiv _ _ α ≫ (N ⋙ R).map s) :
    M.map r ≫ c = α ≫ s := by
  apply ((a.comp b).homEquiv _ _).injective
  rw [compositeMate, hd, Adjunction.homEquiv_naturality_right]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Maps from pulled-back continuous integer coefficients to one finite constant quotient
commute with base change when their adjunction mates give the same finite labeling.

Source: blueprint main-20261015, coefficient pullback proof, second paragraph;
Steps 1--2 of `det-prop-sfb-qlbar-colimit-x-pullback`.
(blueprint: lem-sfb-finite-reduction-pullback)

Proof in words. The canonical constant-sheaf pullback comparison preserves constant
sections, by uniqueness of adjoints for the constant/global-sections adjunction.
The constant-ring/underlying-abelian-group comparison also preserves these sections.
Naturality of a finite-label representation for maps from a singleton determines its
value on each constant label, since the relative singleton test object is terminal.
The two finite-label maps therefore agree on the constant presheaf. Local surjectivity
of its sheafification unit and separatedness of the represented target extend this
equality to every finite section. The inverse-image compositor is the adjunction mate
of the direct-image compositor; its existing unit identity says that the mate of
upperStarFromPointComp is the point unit followed by restriction along fibre-product
associativity. Take mates of the required equality under the point and f adjunctions.
For each continuous section g, apply the preceding finite-label equality and the two
assumed formulas. Naturality of fibre-product associativity for g followed by q
identifies the resulting represented maps. Cancel the finite-label representation
and then the composite adjunction. The argument includes the empty test object and
the empty base scheme. -/
theorem sfb_finite_reduction_pullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (aX : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (aY : sfbFiniteConstantSets Y ≅ sfbFiniteRepresentables Y)
    (q : sfbIntegralProfinite l E ⟶
      FintypeCat.toProfinite.obj (sfbIntegralFiniteLevel l E n))
    (rX : (coefficientRing X (sfbCondensedIntegers l E)).X ⟶
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (integralCoefficientSheaf l E X n))
    (rY : (coefficientRing Y (sfbCondensedIntegers l E)).X ⟶
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (integralCoefficientSheaf l E Y n))
    (hX : ∀ (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E),
      (sfbIntegralFiniteRepresentation l E X aX n).hom.app
          (op ((profiniteToProEtOf X).obj S))
        (rX.hom.app (op ((profiniteToProEtOf X).obj S))
          (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
            (op S) (ULift.up g.hom.hom))) =
        ULift.up ((profiniteToProEtOf X).map (g ≫ q)))
    (hY : ∀ (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E),
      (sfbIntegralFiniteRepresentation l E Y aY n).hom.app
          (op ((profiniteToProEtOf Y).obj S))
        (rY.hom.app (op ((profiniteToProEtOf Y).obj S))
          (((sfbIntegralPointAdjunction Y).unit.app (sfbCondensedIntegers l E).X).hom.app
            (op S) (ULift.up g.hom.hom))) =
        ULift.up ((profiniteToProEtOf Y).map (g ≫ q))) :
    (f)^*[Ab.{u + 1}].map rY ≫ (sfbFiniteCoefficientPullbackIso l E f n).hom =
      ((upperStarFromPointComp f).app (sfbCondensedIntegers l E).X).hom ≫ rX := by
  apply pullbackSquareOfMates (sfbIntegralPointAdjunction Y)
    (upperStarLowerStarAdjunction Ab.{u + 1} f) rY
    (sfbFiniteCoefficientPullbackIso l E f n).hom
    ((upperStarFromPointComp f).hom.app (sfbCondensedIntegers l E).X) rX
    (finiteMate f (Padic.coefficientExtensionRing l E (n + 1)))
    (finiteCoefficient_mate l E f n)
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  induction S using Opposite.rec with | _ S => ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.comp_map, pointLowerStar_map_app, lowerStar_map_hom_app']
  change _ = (((((sfbIntegralPointAdjunction Y).comp
    (upperStarLowerStarAdjunction Ab.{u + 1} f)).homEquiv _ _
      ((upperStarFromPointComp f).hom.app (sfbCondensedIntegers l E).X)).hom.app (op S)) ≫ _)
  rw [point_unit]
  rw [Adjunction.homEquiv_unit]
  repeat' first
    | rw [ObjectProperty.FullSubcategory.comp_hom]
    | rw [NatTrans.comp_app]
    | rw [pointAdj_map_app]
    | rw [pointLowerStar_map_app]
    | rw [lowerStar_map_hom_app']
  simp only [Category.assoc]
  have hr := rX.hom.naturality ((testBaseChange f).hom.app S).op
  change ((upperStarFromPoint X).obj (sfbCondensedIntegers l E).X).obj.map
      ((testBaseChange f).hom.app S).op ≫ _ = _ at hr
  refine Eq.trans ?_ (precomposeEq
    (((sfbIntegralPointAdjunction X).unit.app
      (sfbCondensedIntegers l E).X).hom.app (op S)) hr.symm)
  ext x
  let R := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite R := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.le_add_left 1 n)
  let V := op ((profiniteToProEtOf Y).obj S)
  let W := op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V.unop)
  let g : S ⟶ sfbIntegralProfinite l E := ConcreteCategory.ofHom x.down
  apply ((finiteRepresentation X aX R).app W).toEquiv.injective
  have hm := ConcreteCategory.congr_hom
    (congr_app (finiteRepresentation_mate f aX aY R) V)
      (rY.hom.app V
        (((sfbIntegralPointAdjunction Y).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S) x))
  have hn := ConcreteCategory.congr_hom
    ((finiteRepresentation X aX R).hom.naturality ((testBaseChange f).hom.app S).op)
      (rX.hom.app (op ((profiniteToProEtOf X).obj S))
        (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S) x))
  have hx := hX S g
  have hy := hY S g
  change (finiteRepresentation X aX R).hom.app W
      ((finiteMate f R).hom.app V (rY.hom.app V
        (((sfbIntegralPointAdjunction Y).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S) x))) =
    ULift.up ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
      (((finiteRepresentation Y aY R).hom.app V (rY.hom.app V
        (((sfbIntegralPointAdjunction Y).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S) x))).down) ≫
        (testBaseChange f).hom.app (FintypeCat.toProfinite.obj (FintypeCat.of R))) at hm
  change (finiteRepresentation X aX R).hom.app W
      ((finiteAbSheaf X R).obj.map ((testBaseChange f).hom.app S).op
        (rX.hom.app (op ((profiniteToProEtOf X).obj S))
          (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
            (op S) x))) =
    ULift.up ((testBaseChange f).hom.app S ≫
      (((finiteRepresentation X aX R).hom.app (op ((profiniteToProEtOf X).obj S))
        (rX.hom.app (op ((profiniteToProEtOf X).obj S))
          (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
            (op S) x))).down)) at hn
  change (finiteRepresentation X aX R).hom.app (op ((profiniteToProEtOf X).obj S))
    (rX.hom.app (op ((profiniteToProEtOf X).obj S))
      (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
        (op S) x)) = ULift.up ((profiniteToProEtOf X).map (g ≫ q)) at hx
  change (finiteRepresentation Y aY R).hom.app V
    (rY.hom.app V
      (((sfbIntegralPointAdjunction Y).unit.app (sfbCondensedIntegers l E).X).hom.app
        (op S) x)) = ULift.up ((profiniteToProEtOf Y).map (g ≫ q)) at hy
  rw [hy] at hm
  rw [hx] at hn
  have he := (testBaseChange f).hom.naturality (g ≫ q)
  change (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
      ((profiniteToProEtOf Y).map (g ≫ q)) ≫
        (testBaseChange f).hom.app (FintypeCat.toProfinite.obj (FintypeCat.of R)) =
    (testBaseChange f).hom.app S ≫ (profiniteToProEtOf X).map (g ≫ q) at he
  exact hm.trans ((congrArg ULift.up he).trans hn.symm)


end AlgebraicGeometry.ProEtale
