/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologyLimit

/-!
# Pullback naturality of the etale–pro-etale cohomology comparison

Source: Stacks Project, Cohomology on Sites, Tags 0D6E and 08J6, Section 072X;
Pro-etale Cohomology, Tag 099W; latest blueprint, det-def-purity-conv,
base-change compatibility of the Kummer class
(blueprint: lem-sfb-etale-proetale-comparison-pullback-naturality).

## Main definitions

* `AlgebraicGeometry.ProEtale.cohomologyMap`: canonical pro-etale cohomology pullback.

## Main statements

* `AlgebraicGeometry.ProEtale.comparisonCohomologyMap_pullback`: the comparison square.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

private theorem homEquiv_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') {M : C} {N : E} (f : (L ⋙ L').obj M ⟶ N) :
    (a.comp b).homEquiv M N f = a.homEquiv M _ (b.homEquiv _ N f) := by
  rw [Adjunction.comp_homEquiv]
  rfl

private theorem constant_comparison_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {K : C ⥤ D} {S : D ⥤ C} {K' : C ⥤ E} {S' : E ⥤ C}
    {L : D ⥤ E} {R : E ⥤ D}
    (c : K ⊣ S) (d : K' ⊣ S') (a : L ⊣ R) (r : R ⋙ S ≅ S') (M : C) :
    (c.comp a).homEquiv M (K'.obj M)
        ((((c.comp a).ofNatIsoRight r).leftAdjointUniq d).hom.app M) =
      d.unit.app M ≫ r.inv.app (K'.obj M) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((c.comp a).ofNatIsoRight r) d M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  apply (cancel_mono (r.hom.app (K'.obj M))).1
  calc
    _ = d.unit.app M := h
    _ = (d.unit.app M ≫ r.inv.app _) ≫ r.hom.app _ := by
      rw [Category.assoc, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm

private theorem homEquiv_change_right
    {C D : Type*} [Category C] [Category D]
    {K : C ⥤ D} {S S' : D ⥤ C}
    (c : K ⊣ S) (c' : K ⊣ S') {M : C} {N : D} (f : K.obj M ⟶ N) :
    c'.homEquiv M N f = c.homEquiv M N f ≫ (c.rightAdjointUniq c').hom.app N := by
  simp only [Adjunction.homEquiv_unit, Category.assoc]
  rw [(c.rightAdjointUniq c').hom.naturality]
  simp only [← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]

private theorem constant_comparison_change
    {C D E : Type*} [Category C] [Category D] [Category E]
    {K : C ⥤ D} {S S' : D ⥤ C} {K' : C ⥤ E} {T T' : E ⥤ C}
    {L : D ⥤ E} {R : E ⥤ D}
    (c : K ⊣ S) (c' : K ⊣ S') (d : K' ⊣ T) (d' : K' ⊣ T')
    (a : L ⊣ R) (r : R ⋙ S' ≅ T') (M : C) :
    (c'.comp a).homEquiv M (K'.obj M)
      ((((c.comp a).ofNatIsoRight
        (Functor.isoWhiskerLeft R (c.rightAdjointUniq c') ≪≫ r ≪≫
          (d.rightAdjointUniq d').symm)).leftAdjointUniq d).hom.app M) =
      d'.unit.app M ≫ r.inv.app (K'.obj M) := by
  rw [homEquiv_comp, homEquiv_change_right c c']
  rw [← homEquiv_comp, constant_comparison_unit]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app]
  rw [← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
  erw [Category.comp_id]

private theorem homEquiv_uniq
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R)
    {M : C} {N : D} (f : L'.obj M ⟶ N) :
    a.homEquiv M N ((a.leftAdjointUniq b).hom.app M ≫ f) = b.homEquiv M N f := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]

private theorem constant_comparison_comp
    {C D E Q : Type*} [Category C] [Category D] [Category E] [Category Q]
    {K : C ⥤ D} {S : D ⥤ C} {K' : C ⥤ E} {S' : E ⥤ C}
    {K'' : C ⥤ Q} {S'' : Q ⥤ C}
    {L : D ⥤ E} {R : E ⥤ D} {L' : E ⥤ Q} {R' : Q ⥤ E}
    (c : K ⊣ S) (d : K' ⊣ S') (q : K'' ⊣ S'')
    (a : L ⊣ R) (b : L' ⊣ R') (ra : R ⋙ S ≅ S') (rb : R' ⋙ S' ≅ S'')
    (M : C) (ca : L.obj (K.obj M) ⟶ K'.obj M)
    (cb : L'.obj (K'.obj M) ⟶ K''.obj M)
    (ha : (c.comp a).homEquiv M _ ca = d.unit.app M ≫ ra.inv.app _)
    (hb : (d.comp b).homEquiv M _ cb = q.unit.app M ≫ rb.inv.app _) :
    (c.comp (a.comp b)).homEquiv M _ (L'.map ca ≫ cb) =
      q.unit.app M ≫ rb.inv.app _ ≫ ra.inv.app (R'.obj (K''.obj M)) := by
  rw [homEquiv_comp c (a.comp b), homEquiv_comp a b,
    b.homEquiv_naturality_left, a.homEquiv_naturality_right,
    c.homEquiv_naturality_right, ← homEquiv_comp c a]
  change (c.comp a).homEquiv M _ ca ≫ S.map (R.map (b.homEquiv _ _ cb)) = _
  rw [ha]
  simp only [Category.assoc]
  erw [← ra.inv.naturality]
  change d.unit.app M ≫ S'.map (b.homEquiv _ _ cb) ≫ ra.inv.app _ = _
  rw [← Category.assoc]
  rw [homEquiv_comp, Adjunction.homEquiv_unit] at hb
  rw [hb, Category.assoc]

private theorem constantSheafAdj_homEquiv
    {C A : Type*} [Category C] [Category A] (J : GrothendieckTopology C)
    [HasWeakSheafify J A] {T : C} (hT : CategoryTheory.Limits.IsTerminal T)
    {M : A} {F : Sheaf J A} (f : (constantSheaf J A).obj M ⟶ F) :
    (constantSheafAdj J A hT).homEquiv M F f =
      ((sheafificationAdjunction J A).homEquiv _ F f).app (Opposite.op T) := by
  unfold constantSheafAdj
  erw [homEquiv_comp, Adjunction.homEquiv_unit]
  simp only [constantPresheafAdj_unit_app, Category.id_comp]
  rfl

private theorem constantSheafAdj_homEquiv_naturality
    {C A : Type*} [Category C] [Category A] (J : GrothendieckTopology C)
    [HasWeakSheafify J A] {T U : C}
    (hT : CategoryTheory.Limits.IsTerminal T) (hU : CategoryTheory.Limits.IsTerminal U)
    {M : A} {F : Sheaf J A} (f : (constantSheaf J A).obj M ⟶ F) (g : U ⟶ T) :
    (constantSheafAdj J A hT).homEquiv M F f ≫ F.obj.map g.op =
      (constantSheafAdj J A hU).homEquiv M F f := by
  simp only [constantSheafAdj_homEquiv]
  simpa using (((sheafificationAdjunction J A).homEquiv _ F f).naturality g.op).symm

private theorem constantSheafAdj_unit_naturality
    {C A : Type*} [Category C] [Category A] (J : GrothendieckTopology C)
    [HasWeakSheafify J A] {T U : C}
    (hT : CategoryTheory.Limits.IsTerminal T) (hU : CategoryTheory.Limits.IsTerminal U)
    (M : A) (g : U ⟶ T) :
    (constantSheafAdj J A hT).unit.app M ≫
        ((constantSheaf J A).obj M).obj.map g.op =
      (constantSheafAdj J A hU).unit.app M := by
  simpa only [Adjunction.homEquiv_id] using constantSheafAdj_homEquiv_naturality J hT hU
    (M := M) (F := (constantSheaf J A).obj M) (𝟙 _) g

private noncomputable abbrev comparisonTerminal (X : Scheme.{u}) :=
  (Scheme.toProEt X).obj (⊤_ X.Etale)

private noncomputable abbrev comparisonTerminalIsTerminal (X : Scheme.{u}) :=
  CategoryTheory.Limits.terminalIsTerminal.isTerminalObj (Scheme.toProEt X)

set_option maxHeartbeats 1600000 in
-- The canonical adjunction comparisons involve large functors on the two scheme sites.
private theorem comparison_constant_unit (X : Scheme.{u}) (M : AddCommGrpCat.{u + 1}) :
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      CategoryTheory.Limits.terminalIsTerminal).comp
        (comparisonAdjunction AddCommGrpCat.{u + 1} X)).homEquiv M _
          ((comparisonConstantSheafIso X).hom.app M) =
      (constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
        (comparisonTerminalIsTerminal X)).unit.app M := by
  dsimp only [comparisonAdjunction, comparisonUpperStar, comparisonLowerStar]
  simp only [comparisonConstantSheafIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.sheafPullbackConstruction.sheafPullbackIso,
    homEquiv_comp]
  rw [Adjunction.leftAdjointUniq_inv_app]
  refine (congrArg
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      CategoryTheory.Limits.terminalIsTerminal).homEquiv M _)
    (homEquiv_uniq
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt X)
        AddCommGrpCat.{u + 1} X.smallEtaleTopology (Scheme.ProEt.topology X))
      ((Scheme.toProEt X).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology (Scheme.ProEt.topology X))
      (((Scheme.toProEt X).constantSheafsheafPullbackIso AddCommGrpCat.{u + 1}
        X.smallEtaleTopology (Scheme.ProEt.topology X)
        CategoryTheory.Limits.terminalIsTerminal (comparisonTerminalIsTerminal X)).hom.app
          M))).trans ?_
  rw [← homEquiv_comp]
  change ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    CategoryTheory.Limits.terminalIsTerminal).comp
      ((Scheme.toProEt X).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology (Scheme.ProEt.topology X))).homEquiv M _
          (((Scheme.toProEt X).constantSheafsheafPullbackIso AddCommGrpCat.{u + 1}
            X.smallEtaleTopology (Scheme.ProEt.topology X)
            CategoryTheory.Limits.terminalIsTerminal
            (CategoryTheory.Limits.terminalIsTerminal.isTerminalObj
              (Scheme.toProEt X))).hom.app M) = _
  exact (constant_comparison_unit
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      CategoryTheory.Limits.terminalIsTerminal)
    (constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
      (comparisonTerminalIsTerminal X))
    ((Scheme.toProEt X).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology (Scheme.ProEt.topology X))
    ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
      AddCommGrpCat.{u + 1} X.smallEtaleTopology (Scheme.ProEt.topology X)
      (Opposite.op (⊤_ X.Etale))) M).trans (Category.comp_id _)

private theorem homEquiv_conjugate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (d : R' ≅ R)
    {M : C} {N : D} (t : L'.obj M ⟶ N) :
    a.homEquiv M N (((conjugateEquiv b a).symm d.hom).app M ≫ t) =
      b.homEquiv M N t ≫ d.hom.app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← unit_conjugateEquiv_symm b a d.hom M]
  simp only [Category.assoc, d.hom.naturality]

private noncomputable abbrev proEtaleMkIdSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  NatIso.ofComponents (fun (_ : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) ↦
      Iso.refl _) ≪≫
    ((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).mapIso
      (overPullbackObjMkIdIso f).op).symm

private noncomputable abbrev proEtaleTerminalIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj (comparisonTerminal Y) ≅
      comparisonTerminal X :=
  (Scheme.toProEt X).mapIso (CategoryTheory.Limits.PreservesTerminal.iso f.Etale)

private noncomputable abbrev proEtaleSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    lowerStar AddCommGrpCat.{u + 1} f ⋙
      (sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
        (Opposite.op (comparisonTerminal Y)) ≅
    (sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (Opposite.op (comparisonTerminal X)) :=
  NatIso.ofComponents (fun (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) ↦
    H.obj.mapIso (proEtaleTerminalIso f).op.symm)
    (fun α ↦ (α.hom.naturality _).symm)

private theorem proEtale_constant_mkId_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : AddCommGrpCat.{u + 1}) :
    ((constantSheafAdj (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.isTerminalMkId Y)).comp
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)).homEquiv M _
          ((constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} f).hom.app M) =
      (constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
        (Scheme.ProEt.isTerminalMkId X)).unit.app M ≫
          (proEtaleMkIdSectionsIso f).inv.app _ := by
  exact constant_comparison_change
    (constantSheafΓAdj (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (constantSheafAdj (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.isTerminalMkId Y))
    (constantSheafΓAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.isTerminalMkId X))
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) (proEtaleMkIdSectionsIso f) M

private theorem proEtale_constant_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : AddCommGrpCat.{u + 1}) :
    ((constantSheafAdj (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}
      (comparisonTerminalIsTerminal Y)).comp
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)).homEquiv M _
          ((constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} f).hom.app M) =
      (constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
        (comparisonTerminalIsTerminal X)).unit.app M ≫
          (proEtaleSectionsIso f).inv.app _ := by
  let P := (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj M
  let hy := (Scheme.ProEt.isTerminalMkId Y).from (comparisonTerminal Y)
  let hx := (Scheme.ProEt.isTerminalMkId X).from (comparisonTerminal X)
  rw [homEquiv_comp]
  rw [← constantSheafAdj_homEquiv_naturality _ (Scheme.ProEt.isTerminalMkId Y)
    (comparisonTerminalIsTerminal Y) _ hy, ← homEquiv_comp,
    proEtale_constant_mkId_unit]
  rw [← constantSheafAdj_unit_naturality _ (Scheme.ProEt.isTerminalMkId X)
    (comparisonTerminalIsTerminal X) M hx]
  change (_ ≫ P.obj.map (overPullbackObjMkIdIso f).hom.op) ≫
      P.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map hy).op =
    (_ ≫ P.obj.map hx.op) ≫ P.obj.map (proEtaleTerminalIso f).hom.op
  simp only [Category.assoc, ← Functor.map_comp, ← CategoryTheory.op_comp]
  have hh :
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map hy ≫
          (overPullbackObjMkIdIso f).hom =
        (proEtaleTerminalIso f).hom ≫ hx :=
    (Scheme.ProEt.isTerminalMkId X).hom_ext _ _
  rw [hh]

private theorem comparison_constant_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : AddCommGrpCat.{u + 1}) :
    (supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).hom.app
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ≫
      (upperStar AddCommGrpCat.{u + 1} f).map ((comparisonConstantSheafIso Y).hom.app M) ≫
        (constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} f).hom.app M =
      (comparisonUpperStar AddCommGrpCat.{u + 1} X).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app M) ≫
        (comparisonConstantSheafIso X).hom.app M := by
  let cY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    CategoryTheory.Limits.terminalIsTerminal
  let cX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    CategoryTheory.Limits.terminalIsTerminal
  let pY := constantSheafAdj (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}
    (comparisonTerminalIsTerminal Y)
  let pX := constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
    (comparisonTerminalIsTerminal X)
  let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let n := comparisonAdjunction AddCommGrpCat.{u + 1} Y
  let n' := comparisonAdjunction AddCommGrpCat.{u + 1} X
  let b := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let d := supportSiteComparisonCoefficientDirectImageIso AddCommGrpCat.{u + 1} f
  apply ((cY.comp (a.comp n')).homEquiv M _).injective
  rw [homEquiv_comp]
  change cY.homEquiv M _ ((a.comp n').homEquiv _ _
    (((conjugateEquiv (n.comp b) (a.comp n')).symm d.hom).app _ ≫ _)) = _
  rw [homEquiv_conjugate, Adjunction.homEquiv_naturality_right]
  rw [← homEquiv_comp]
  have hn : (cY.comp n).homEquiv M _ ((comparisonConstantSheafIso Y).hom.app M) =
      pY.unit.app M := comparison_constant_unit Y M
  have hn' : (cX.comp n').homEquiv M _ ((comparisonConstantSheafIso X).hom.app M) =
      pX.unit.app M := comparison_constant_unit X M
  have ha : (cY.comp a).homEquiv M _
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app M) =
      cX.unit.app M ≫
        (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f).inv.app _ := by
    exact constant_comparison_unit cY cX a _ M
  rw [constant_comparison_comp cY pY pX n b (Iso.refl _) (proEtaleSectionsIso f) M
    _ _ (hn.trans (Category.comp_id _).symm) (proEtale_constant_unit f M)]
  rw [constant_comparison_comp cY cX pX a n'
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f) (Iso.refl _) M
    _ _ ha (hn'.trans (Category.comp_id _).symm)]
  simp only [Iso.refl_inv, NatTrans.id_app]
  let P := (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj M
  let W := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj (comparisonTerminal Y)
  suffices
      pX.unit.app M ≫ P.obj.map (proEtaleTerminalIso f).hom.op ≫
          P.obj.map (𝟙 W).op =
        pX.unit.app M ≫ P.obj.map (proEtaleTerminalIso f).hom.op by
    simpa [-CategoryTheory.Functor.map_id, -CategoryTheory.op_id,
      P, W, comparisonLowerStar, Etale.lowerStar, lowerStar,
      Functor.sheafPushforwardContinuous, proEtaleSectionsIso, proEtaleTerminalIso,
      Etale.lowerStarCompSheafSectionsTerminalIso, d,
      supportSiteComparisonCoefficientDirectImageIso, supportSiteComparisonSiteBaseChangeIso,
      Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans] using this
  erw [CategoryTheory.op_id, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem inverse_square
    {C : Type*} [Category C] {A B D E T : C}
    (k : A ≅ B) (n : B ≅ D) (b : D ≅ T) (a : A ≅ E) (m : E ≅ T)
    (h : k.hom ≫ n.hom ≫ b.hom = a.hom ≫ m.hom) :
    b.inv ≫ n.inv = m.inv ≫ a.inv ≫ k.hom := by
  apply (cancel_mono (n.hom ≫ b.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  rw [h]
  simp

/-- The canonical etale–pro-etale comparison commutes with pullback for every abelian
sheaf in every nonnegative degree. The sheaf comparison has direction
`ν_X⁻¹ f_et⁻¹ F ⟶ f_proet⁻¹ ν_Y⁻¹ F`.
Source: Stacks Project, Tags 0D6E, 08J6 and 099W, Section 072X; latest blueprint,
det-def-purity-conv, base-change compatibility of the Kummer class
(blueprint: lem-sfb-etale-proetale-comparison-pullback-naturality).

Proof:
1. Each constant-sheaf comparison is the left-adjoint uniqueness isomorphism of the
   composite adjunctions, and the comparison `κ` is the unit-normalized conjugate of the
   canonical direct-image isomorphism (`lem-weil-pbc-comparison-pullback`,
   `lem-weil-pbc-conjugate-iso-unit-equation`). Transposed under the composite
   adjunctions, both ways from `ν_X⁻¹ f_et⁻¹ ℤ` to the pro-etale constant sheaf `ℤ` on `X`
   become restriction along maps from the base change of the terminal `Y`-object to the
   terminal `X`-object; these agree, which gives the square of constant-sheaf comparisons.
2. Global cohomology is Ext from the constant sheaf `ℤ`, and all four maps apply an exact
   inverse image to the Ext class and precompose with the inverse constant-sheaf
   comparison (`lem-cbc-abelian-etale-proetale-cohomology-comparison`,
   `def-weil-pbc-cohomology-pullback`). Inverting the square of step 1,
   `lem-weil-pbc-ext-exact-functor-composition-comparison` for `κ` and for the identity of
   the composite, `mk₀` multiplicativity and associativity of Yoneda composition give the
   equality in every degree. No finiteness, torsion or morphism restriction is used. -/
theorem comparisonCohomologyMap_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyMap f ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj F) i).comp
        (comparisonCohomologyMap Y F i) =
      (Sheaf.H.map
        ((supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).hom.app F)
        i).comp
          ((comparisonCohomologyMap X ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)
            i).comp (Etale.cohomologyMap f F i)) := by
  -- Use the defining Ext maps directly, after checking their constant-sheaf square.
  let a := Etale.upperStar AddCommGrpCat.{u + 1} f
  let n := comparisonUpperStar AddCommGrpCat.{u + 1} Y
  let n' := comparisonUpperStar AddCommGrpCat.{u + 1} X
  let b := upperStar AddCommGrpCat.{u + 1} f
  let k : a ⋙ n' ≅ n ⋙ b :=
    supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f
  let C := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let ca := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
    (AddCommGrpCat.of (ULift ℤ))
  let cn := (comparisonConstantSheafIso Y).app (AddCommGrpCat.of (ULift ℤ))
  let cn' := (comparisonConstantSheafIso X).app (AddCommGrpCat.of (ULift ℤ))
  let cb := (constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} f).app
    (AddCommGrpCat.of (ULift ℤ))
  have hc : cb.inv ≫ b.map cn.inv = cn'.inv ≫ n'.map ca.inv ≫ k.hom.app C :=
    inverse_square (k.app C) (b.mapIso cn) cb (n'.mapIso ca) cn'
      (comparison_constant_square f (AddCommGrpCat.of (ULift ℤ)))
  apply AddMonoidHom.ext
  intro x
  change cohomologyMap f _ i (comparisonCohomologyMap Y F i x) =
    Sheaf.H.map _ i (comparisonCohomologyMap X _ i (Etale.cohomologyMap f F i x))
  simp only [cohomologyMap, comparisonCohomologyMap,
    Sheaf.H.mapFunctor_apply, Sheaf.H.map_apply, Etale.cohomologyMap_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  change (Abelian.Ext.mk₀ (cb.inv ≫ b.map cn.inv)).comp
      ((x.mapExactFunctor n).mapExactFunctor b) (zero_add i) =
    ((Abelian.Ext.mk₀ (cn'.inv ≫ n'.map ca.inv)).comp
      ((x.mapExactFunctor a).mapExactFunctor n') (zero_add i)).comp
        (Abelian.Ext.mk₀ (k.hom.app F)) (add_zero i)
  let := CategoryTheory.Limits.comp_preservesFiniteLimits a n'
  let := CategoryTheory.Limits.comp_preservesFiniteColimits a n'
  have hcomp : x.mapExactFunctor (a ⋙ n') =
      (x.mapExactFunctor a).mapExactFunctor n' := by
    simpa only [Iso.refl_hom, NatTrans.id_app, Abelian.Ext.comp_mk₀_id,
      Abelian.Ext.mk₀_id_comp] using
      Abelian.Ext.mapExactFunctor_comp_mk₀_eq_sheaf a n' (a ⋙ n') (Iso.refl _) x
  rw [hc, ← Category.assoc, ← Abelian.Ext.mk₀_comp_mk₀_assoc,
    ← Abelian.Ext.mapExactFunctor_comp_mk₀_eq_sheaf n b (a ⋙ n') k x,
    hcomp, Abelian.Ext.comp_assoc_of_third_deg_zero]

end AlgebraicGeometry.ProEtale
