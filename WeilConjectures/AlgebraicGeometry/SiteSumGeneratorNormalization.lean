/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRingGraphSummand
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.AlgebraicGeometry.LocalizedPullbackComparisonNormalization

/-! # Generator normalization for the localized etale sum comparison

Source: `WeilConjectures.AlgebraicGeometry.VaryingRingGraphSummand`, finite_normalization, step 1;
Stacks Project, Tags 04J0, 03DI and 03DJ; current blueprint `det-sp-tower-gluing`,
Local pairs and Levels (blueprint: lem-sp-site-sum-generator-normalization).

The comparison is specified by its inverse, the existing canonical sum mate.
Its generator formula and its unit and counit equations use the same adjunctions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem restriction_unit_ext
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (Q : Dᵒᵖ ⥤ E) (P : Cᵒᵖ ⥤ E)
    (rho : P ≅ F.op ⋙ Q) (eta : Q ⟶ G.op ⋙ P)
    (h : ∀ V : D, eta.app (op V) ≫ rho.hom.app (op (G.obj V)) =
      Q.map (a.counit.app V).op)
    (t : P ⟶ F.op ⋙ Q)
    (ht : ∀ V : D, eta.app (op V) ≫ t.app (op (G.obj V)) =
      Q.map (a.counit.app V).op) : t = rho.hom := by
  let b := a.op.whiskerLeft E
  have he : b.homEquiv Q (F.op ⋙ Q) (rho.inv ≫ t) =
      b.homEquiv Q (F.op ⋙ Q) (𝟙 _) := by
    apply NatTrans.ext
    funext V
    simp only [Adjunction.homEquiv_unit, NatTrans.comp_app]
    dsimp [b, Adjunction.whiskerLeft, Adjunction.op]
    simp only [Category.id_comp, Category.comp_id]
    change Q.map (a.counit.app V.unop).op ≫
      (rho.inv.app (op (G.obj V.unop)) ≫ t.app (op (G.obj V.unop))) =
        Q.map (a.counit.app V.unop).op
    calc
      _ = (eta.app V ≫ rho.hom.app (op (G.obj V.unop))) ≫
          (rho.inv.app (op (G.obj V.unop)) ≫ t.app (op (G.obj V.unop))) := by
        rw [h V.unop]
      _ = eta.app V ≫ t.app (op (G.obj V.unop)) := by simp [Category.assoc]
      _ = _ := ht V.unop
  have he' := (b.homEquiv Q (F.op ⋙ Q)).injective he
  apply (cancel_epi rho.inv).1
  simpa using he'

namespace AlgebraicGeometry.ProEtale.VaryingRingGraph

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A]

/-- The comparison unit on a section at an etale test object, in the existing
constant-ring module coordinates. The realization is the unique one preserving
constant sections; the inverse of `cUnderlying` merely expresses its section carrier.
Source: Stacks 099R and 03DA; the generator convention in finite_normalization, step 1
(blueprint: lem-sp-site-sum-generator-normalization). -/
def siteSumUnitSection (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : X.Etale)
    (m : F.obj.obj (op W)) :
    ((sitePull A X).obj F).val.obj (op ((toProEt X).obj W)) :=
  ((StrictTower.cUnderlying A X A (RingHom.id A)).inv.app
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F)).hom.app
      (op ((toProEt X).obj W))
        (((Scheme.proEtaleSiteComparisonModules X A).unit.app F).hom.app (op W) m)

/-- Inclusion of the lift summand on the etale site, using the recorded sum adjunction
and its section-normalized localization comparison.
Source: Stacks 03DI; finite_normalization, step 1
(blueprint: lem-sp-site-sum-generator-normalization). -/
def etaleSumLiftGenerator {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (m : M.obj.obj (op W)) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) :=
  (((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
    inferInstance).unit.app M ≫
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
        inferInstance).hom.app
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).hom.app
            (op W)) m

private theorem scalar_restriction_sections {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (j : StrictTower.C A T A (RingHom.id A) ⋙ StrictTower.modulePullback A e ≅
      upperStar (ModuleCat.{u + 1} A) e ⋙ StrictTower.C A U A (RingHom.id A))
    (hj : j.hom =
      ((mateEquiv (supportSiteProEtaleComparisonAdjunction (ModuleCat.{u + 1} A) e)
        (Scheme.proEtaleRingModuleAdjunction e (StrictTower.coefficients A T)
          (StrictTower.coefficients A U) (StrictTower.constantRingIso A e))).symm
        (StrictTower.cDirect A e A (RingHom.id A)).hom).natTrans)
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (W : U.ProEt)
    (x : ((StrictTower.modulePullback A e).obj
      ((StrictTower.C A T A (RingHom.id A)).obj F)).val.obj (op W)) :
    ((StrictTower.cUnderlying A U A (RingHom.id A)).hom.app
      ((localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj F)).hom.app
        (op W)
        (((StrictTower.C A U A (RingHom.id A)).map
          ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
            inferInstance).hom.app F)).val.app (op W)
          ((j.hom.app F).val.app (op W) x)) =
      ((StrictTower.cUnderlying A T A (RingHom.id A)).hom.app F).hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).obj W))
        (((levelRestrictionComparison A e).hom.app
          ((StrictTower.C A T A (RingHom.id A)).obj F)).val.app (op W) x) := by
  let b := Scheme.proEtaleRingModuleAdjunction e (StrictTower.coefficients A T)
    (StrictTower.coefficients A U) (StrictTower.constantRingIso A e)
  let ar := (levelRestrictionAdjunction_existsUnique A e).exists.choose
  let r := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance
  let Q := (StrictTower.C A T A (RingHom.id A)).obj F
  let P := (StrictTower.modulePullback A e).obj Q
  let S := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)
  let G := proEtaleBaseChange e
  let forgetU := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (StrictTower.coefficients A U)) ⋙
    sheafToPresheaf (ProEt.topology U) AddCommGrpCat.{u + 1}
  let rho : P.val.presheaf ≅ S.op ⋙ Q.val.presheaf :=
    forgetU.mapIso ((levelRestrictionComparison A e).app Q)
  let eta : Q.val.presheaf ⟶ G.op ⋙ P.val.presheaf :=
    ((SheafOfModules.toSheaf _).map (b.unit.app Q)).hom
  let t : P.val.presheaf ⟶ S.op ⋙ Q.val.presheaf :=
    forgetU.map (j.hom.app F) ≫
      forgetU.map ((StrictTower.C A U A (RingHom.id A)).map (r.hom.app F)) ≫
      ((StrictTower.cUnderlying A U A (RingHom.id A)).hom.app
        ((localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj F)).hom ≫
      Functor.whiskerLeft S.op
        (((StrictTower.cUnderlying A T A (RingHom.id A)).inv.app F).hom)
  have hr (V : T.ProEt) : eta.app (op V) ≫ rho.hom.app (op (G.obj V)) =
      Q.val.presheaf.map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e inferInstance
          trivial).counit.app V).op := by
    ext y
    have h := congrArg (fun f ↦ f.val.app (op V) y)
      (b.unit_leftAdjointUniq_hom_app ar Q)
    exact h.trans ((levelRestrictionAdjunction_existsUnique A e).exists.choose_spec Q V y)
  have ht (V : T.ProEt) : eta.app (op V) ≫ t.app (op (G.obj V)) =
      Q.val.presheaf.map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e inferInstance
          trivial).counit.app V).op := by
    have hu : (StrictTower.C A T A (RingHom.id A)).map
          ((supportSiteProEtaleComparisonAdjunction
            (ModuleCat.{u + 1} A) e).unit.app F) ≫
        (StrictTower.cDirect A e A (RingHom.id A)).hom.app
          ((upperStar (ModuleCat.{u + 1} A) e).obj F) =
        b.unit.app Q ≫ (StrictTower.moduleDirectImage A e).map (j.hom.app F) := by
      rw [hj]
      exact unit_mateEquiv_symm
        (supportSiteProEtaleComparisonAdjunction (ModuleCat.{u + 1} A) e) b
        (StrictTower.cDirect A e A (RingHom.id A)).hom F
    have hn := (LocalizedPullback.normalization A e).2.1.1 F V
    have nr := (StrictTower.cUnderlying A U A (RingHom.id A)).hom.naturality
      (r.hom.app F)
    have ne := (StrictTower.cUnderlying A T A (RingHom.id A)).hom.naturality
      ((supportSiteProEtaleComparisonAdjunction (ModuleCat.{u + 1} A) e).unit.app F)
    ext y
    let y' := ((StrictTower.C A T A (RingHom.id A)).map
      ((supportSiteProEtaleComparisonAdjunction (ModuleCat.{u + 1} A) e).unit.app F)
        ).val.app (op V) y
    let z := (j.hom.app F).val.app (op (G.obj V))
      ((b.unit.app Q).val.app (op V) y)
    have hu' := congrArg (fun f ↦ f.val.app (op V) y) hu
    have hd := (StrictTower.cDirect_existsUnique A e A (RingHom.id A)).choose_spec.1
      ((upperStar (ModuleCat.{u + 1} A) e).obj F) (op V) y'
    have hz :
        ((StrictTower.cUnderlying A U A (RingHom.id A)).hom.app
          ((upperStar (ModuleCat.{u + 1} A) e).obj F)).hom.app
            (op (G.obj V)) z =
        ((StrictTower.cUnderlying A T A (RingHom.id A)).hom.app
          ((lowerStar (ModuleCat.{u + 1} A) e).obj
            ((upperStar (ModuleCat.{u + 1} A) e).obj F))).hom.app (op V) y' := by
      rw [← hd]
      exact congrArg
        (((StrictTower.cUnderlying A U A (RingHom.id A)).hom.app
          ((upperStar (ModuleCat.{u + 1} A) e).obj F)).hom.app (op (G.obj V)))
        hu'.symm
    have hnr := ConcreteCategory.congr_hom
      (congr_app (congrArg InducedCategory.Hom.hom nr) (op (G.obj V))) z
    have hne := ConcreteCategory.congr_hom
      (congr_app (congrArg InducedCategory.Hom.hom ne) (op V)) y
    have hnu := ConcreteCategory.congr_hom
      (((StrictTower.cUnderlying A T A (RingHom.id A)).hom.app F).hom.naturality
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
          inferInstance trivial).counit.app V).op) y
    have hhn := ConcreteCategory.congr_hom hn
      (((StrictTower.cUnderlying A T A (RingHom.id A)).hom.app F).hom.app (op V) y)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      comp_apply] at hnr hne hhn hnu
    have hz' :
        ((StrictTower.cUnderlying A U A (RingHom.id A)).hom.app
          ((localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj F)).hom.app
            (op (G.obj V))
            (((StrictTower.C A U A (RingHom.id A)).map (r.hom.app F)).val.app
              (op (G.obj V)) z) =
        F.obj.map
          ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
            inferInstance trivial).counit.app V).op
          (((StrictTower.cUnderlying A T A (RingHom.id A)).hom.app F).hom.app (op V) y) :=
      (hnr.trans (congrArg ((r.hom.app F).hom.app (op (G.obj V))) hz)).trans
        ((congrArg ((r.hom.app F).hom.app (op (G.obj V))) hne).trans hhn)
    have hproj := hz'.trans hnu.symm
    have hproj' := congrArg
      (((StrictTower.cUnderlying A T A (RingHom.id A)).inv.app F).hom.app
        (op (S.obj (G.obj V)))) hproj
    have hi := ConcreteCategory.congr_hom
      (congr_app (congrArg InducedCategory.Hom.hom
        ((StrictTower.cUnderlying A T A (RingHom.id A)).hom_inv_id_app F))
          (op (S.obj (G.obj V))))
      (Q.val.presheaf.map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
          inferInstance trivial).counit.app V).op y)
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app, NatTrans.id_app,
      ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hi
    exact hproj'.trans hi
  have he := restriction_unit_ext
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e inferInstance trivial)
    Q.val.presheaf P.val.presheaf rho eta hr t ht
  have hx := ConcreteCategory.congr_hom (congr_app he (op W)) x
  have hx' := congrArg
    (((StrictTower.cUnderlying A T A (RingHom.id A)).hom.app F).hom.app
      (op (S.obj W))) hx
  let v := ((StrictTower.cUnderlying A U A (RingHom.id A)).hom.app
      ((localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj F)).hom.app
        (op W)
        (((StrictTower.C A U A (RingHom.id A)).map (r.hom.app F)).val.app (op W)
          ((j.hom.app F).val.app (op W) x))
  have hi := ConcreteCategory.congr_hom
    (congr_app (congrArg InducedCategory.Hom.hom
      ((StrictTower.cUnderlying A T A (RingHom.id A)).inv_hom_id_app F))
        (op (S.obj W))) v
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app, NatTrans.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hi
  exact hi.symm.trans hx'

private theorem site_pullback_unit_section {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (x : F.obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))) :
    ((levelRestrictionComparison A e).hom.app ((sitePull A T).obj F)).val.app
        (op ((toProEt U).obj W))
        (((@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
          (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))).app F).val.app
          (op ((toProEt U).obj W))
          (((sitePull A U).map
            ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
              inferInstance).inv.app F)).val.app (op ((toProEt U).obj W))
            (siteSumUnitSection A U
              ((Etale.localizationRestriction (ModuleCat.{u + 1} A) e
                inferInstance).obj F) W x))) =
      siteSumUnitSection A T F
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) x := by
  obtain ⟨j, hj, hcomp, hchi⟩ := (LocalizedPullback.normalization A e).2.2.2.2.2
  let rF := (Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj F
  let w := (toProEt U).obj W
  let q := ((Scheme.proEtaleSiteComparisonModules U A).unit.app rF).hom.app (op W) x
  let z := siteSumUnitSection A U rF W x
  let f := (sitePull A U).map
    ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
      inferInstance).inv.app F)
  let p := (@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
    (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))).app F
  have hz : ((StrictTower.cUnderlying A U A (RingHom.id A)).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj rF)).hom.app (op w) z = q := by
    simpa only [z, q, siteSumUnitSection, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app, NatTrans.id_app,
      comp_apply, id_apply] using
      ConcreteCategory.congr_hom
        (congr_app (congrArg InducedCategory.Hom.hom
          ((StrictTower.cUnderlying A U A (RingHom.id A)).inv_hom_id_app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj rF))) (op w)) q
  have hc := congrArg (fun t ↦ t.app F) hchi
  have hc' := congrArg (fun t ↦ t.val.app (op w) z) hc
  have hs := scalar_restriction_sections A e j hj
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) w
    (p.val.app (op w) (f.val.app (op w) z))
  have hn := (LocalizedPullback.normalization A e).2.2.2.2.1 F
  have hn' := congrArg (fun t ↦ t.hom.app (op W) x) hn
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F
  let E := (StrictTower.cUnderlying A T A (RingHom.id A)).hom.app N
  apply (ConcreteCategory.bijective_of_isIso
    (E.hom.app
      (op ((toProEt T).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))))).injective
  have nc := (StrictTower.cUnderlying A U A (RingHom.id A)).hom.naturality
    ((LocalizedPullback.chi A e).hom.app F)
  have nc' := congrArg (fun t ↦ t.hom.app (op w) z) nc
  have hh : E.hom.app
      (op ((toProEt T).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
      (((levelRestrictionComparison A e).hom.app ((sitePull A T).obj F)).val.app
        (op w) (p.val.app (op w) (f.val.app (op w) z))) =
      ((LocalizedPullback.chi A e).hom.app F).hom.app (op w) q := by
    exact hs.symm.trans
      ((congrArg
        (((StrictTower.cUnderlying A U A (RingHom.id A)).hom.app
          ((localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj N)).hom.app
            (op w)) hc').trans
        (nc'.trans (congrArg
          (((LocalizedPullback.chi A e).hom.app F).hom.app (op w)) hz)))
  rw [hh]
  change _ = E.hom.app _
    (((StrictTower.cUnderlying A T A (RingHom.id A)).inv.app N).hom.app _
      (((Scheme.proEtaleSiteComparisonModules T A).unit.app F).hom.app _ x))
  rw [show E.hom.app _
      (((StrictTower.cUnderlying A T A (RingHom.id A)).inv.app N).hom.app _
        (((Scheme.proEtaleSiteComparisonModules T A).unit.app F).hom.app _ x)) =
      ((Scheme.proEtaleSiteComparisonModules T A).unit.app F).hom.app _ x from
    ConcreteCategory.congr_hom
      (congr_app (congrArg InducedCategory.Hom.hom
        ((StrictTower.cUnderlying A T A (RingHom.id A)).inv_hom_id_app N)) _)
      (((Scheme.proEtaleSiteComparisonModules T A).unit.app F).hom.app _ x)]
  simp only [LocalizedPullback.beta, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, comp_apply] at hn'
  exact hn'

private theorem siteSumUnitSection_naturality (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (f : F ⟶ G)
    (W : X.Etale) (m : F.obj.obj (op W)) :
    ((sitePull A X).map f).val.app (op ((toProEt X).obj W))
      (siteSumUnitSection A X F W m) =
    siteSumUnitSection A X G W (f.hom.app (op W) m) := by
  let w := op ((toProEt X).obj W)
  have hq := congrArg (fun t ↦ t.hom.app (op W) m)
    ((Scheme.proEtaleSiteComparisonModules X A).unit.naturality f)
  have hc := congrArg (fun t ↦ t.hom.app w
      (((Scheme.proEtaleSiteComparisonModules X A).unit.app F).hom.app (op W) m))
    ((StrictTower.cUnderlying A X A (RingHom.id A)).inv.naturality
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).map f))
  exact hc.symm.trans (congrArg
    (((StrictTower.cUnderlying A X A (RingHom.id A)).inv.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj G)).hom.app w) hq.symm)

/-- The specified sum mate is invertible, fixes the lift index and applies the
comparison unit to its coefficient, and preserves the summand units and fold counits.
Source: finite_normalization, step 1; Stacks 04J0, 03DI, 03DJ and 0B65;
current blueprint Local pairs and Levels
(blueprint: lem-sp-site-sum-generator-normalization).

Proof:
1. The existing theorem `siteSumInv_isIso` makes the specified sum mate h = siteSumInv
invertible; put a = h⁻¹, so the first conjunct holds by definition.
2. The inverse-mate unit identity (`unit_mateEquiv_symm`) for the etale sum adjunction,
the pro-etale sum adjunction and chi = inv hPullbackInv gives N_U(unit) ≫ chi = unit' ≫
R'(h). Composing with R'(a) cancels h ≫ a: the second conjunct. The inverse-mate counit
identity (`mateEquiv_counit_symm`) gives the third after precomposing with a.
3. The two identifications of constant-coefficient pullback with section restriction
agree: `levelRestrictionComparison` and the scalar-change mate j followed by geometric
localization restriction both preserve the projection unit (the latter by
`unit_mateEquiv_symm` for cDirect, the section normalization of cDirect, naturality of
cUnderlying and the projection-unit clause of `LocalizedPullback.normalization`). By
injectivity of the Hom equivalence of the opposite site adjunction whiskered into
additive groups, they agree on every section.
4. The last clause of `LocalizedPullback.normalization`, with beta the identity on
test-object sections, and step 3 send inv hPullbackInv of the comparison-unit section
of x to the comparison-unit section of x on the composed etale test object.
5. The comparison-unit section is natural in the sheaf. Apply step 4 to F = e_!(M) and
the etale lift generator, cancel the etale restriction isomorphism, evaluate the unit
equation of step 2 at the comparison-unit section of m, and use naturality of
`levelRestrictionComparison` for a: the left side is a of the lift generator and the
right side is `levelGenerator`, the fourth conjunct. No sheafification extension is
needed since the clause concerns these specified sections.
-/
theorem siteSum_generator_normalization {U T : Scheme.{u}} (e : U ⟶ T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] :
    ∃ a : Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙ sitePull A T ≅
        sitePull A U ⋙ levelSum A e,
      a.inv = siteSumInv A e ∧
      (∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
        (sitePull A U).map
            ((Etale.etaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) e inferInstance).unit.app M) ≫
          (@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
            (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))).app
              ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ≫
          (StrictTower.modulePullback A e).map (a.hom.app M) =
        (levelSumAdjunction A e).unit.app ((sitePull A U).obj M)) ∧
      (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        a.hom.app ((Etale.upperStar (ModuleCat.{u + 1} A) e).obj F) ≫
          (levelSum A e).map
            ((@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
              (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))).app F) ≫
          (levelSumAdjunction A e).counit.app ((sitePull A T).obj F) =
        (sitePull A T).map
          ((Etale.etaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app F)) ∧
      (∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
          (m : M.obj.obj (op W)),
        (a.hom.app M).val.app
            (op ((toProEt T).obj
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
            (siteSumUnitSection A T
              ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
              (etaleSumLiftGenerator A e M W m)) =
        levelGenerator A e ((sitePull A U).obj M) ((toProEt U).obj W)
          (siteSumUnitSection A U M W m)) := by
  let α := @inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
    (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))
  let h := siteSumInv A e
  have : IsIso h := siteSumInv_isIso A e
  let a := (asIso h).symm
  have ha : a.inv = siteSumInv A e := rfl
  have hu := unit_mateEquiv_symm
    (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (levelSumAdjunction A e)
    (TwoSquare.mk _ _ _ _ α)
  have hc := mateEquiv_counit_symm
    (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (levelSumAdjunction A e)
    (TwoSquare.mk _ _ _ _ α)
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · exact ha
  · intro M
    change (sitePull A U).map ((Etale.etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).unit.app M) ≫ α.app _ ≫
      (StrictTower.modulePullback A e).map (a.hom.app M) = _
    rw [← Category.assoc, hu M, Category.assoc, ← Functor.map_comp]
    change _ ≫ (StrictTower.modulePullback A e).map (h.app M ≫ (inv h).app M) = _
    simp
  · intro F
    change a.hom.app _ ≫ (levelSum A e).map (α.app F) ≫
      (levelSumAdjunction A e).counit.app _ = _
    rw [hc F]
    change (inv h).app _ ≫ (h.app _ ≫ _) = _
    simp
  · intro M W m
    let S := Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance
    let eta := (Etale.etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).unit.app M
    let r := (Etale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} A) e inferInstance).app (S.obj M)
    let w := op ((toProEt U).obj W)
    let z := siteSumUnitSection A U M W m
    let x := etaleSumLiftGenerator A e M W m
    have hn := siteSumUnitSection_naturality A U (eta ≫ r.hom) W m
    have he : (sitePull A U).map (eta ≫ r.hom) ≫ (sitePull A U).map r.inv =
        (sitePull A U).map eta := by
      rw [← Functor.map_comp]
      simp
    have hn' : ((sitePull A U).map (eta ≫ r.hom)).val.app w z =
        siteSumUnitSection A U
          ((Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj
            (S.obj M)) W x := hn
    have hz : ((sitePull A U).map r.inv).val.app w
        (siteSumUnitSection A U
          ((Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj
            (S.obj M)) W x) =
        ((sitePull A U).map eta).val.app w z :=
      (congrArg (((sitePull A U).map r.inv).val.app w) hn'.symm).trans
        (congrArg (fun t ↦ t.val.app w z) he)
    have hb :
        ((levelRestrictionComparison A e).hom.app ((sitePull A T).obj (S.obj M))).val.app w
          ((α.app (S.obj M)).val.app w (((sitePull A U).map eta).val.app w z)) =
        siteSumUnitSection A T (S.obj M)
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) x :=
      (congrArg (fun y ↦
        ((levelRestrictionComparison A e).hom.app ((sitePull A T).obj (S.obj M))).val.app w
          ((α.app (S.obj M)).val.app w y)) hz.symm).trans
        (site_pullback_unit_section A e (S.obj M) W x)
    have hunit : (sitePull A U).map eta ≫ α.app (S.obj M) ≫
        (StrictTower.modulePullback A e).map (a.hom.app M) =
        (levelSumAdjunction A e).unit.app ((sitePull A U).obj M) := by
      rw [← Category.assoc, hu M, Category.assoc, ← Functor.map_comp]
      change _ ≫ (StrictTower.modulePullback A e).map (h.app M ≫ (inv h).app M) = _
      simp
    have hr := (levelRestrictionComparison A e).hom.naturality (a.hom.app M)
    have hr' := congrArg (fun t ↦ t.val.app w
      ((α.app (S.obj M)).val.app w (((sitePull A U).map eta).val.app w z))) hr
    have hs := congrArg (fun t ↦
      (t ≫ (levelRestrictionComparison A e).hom.app
        ((levelSum A e).obj ((sitePull A U).obj M))).val.app w z) hunit
    have hs' : (a.hom.app M).val.app
        (op ((toProEt T).obj
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (((levelRestrictionComparison A e).hom.app
          ((sitePull A T).obj (S.obj M))).val.app w
            ((α.app (S.obj M)).val.app w (((sitePull A U).map eta).val.app w z))) =
        levelGenerator A e ((sitePull A U).obj M) ((toProEt U).obj W) z :=
      hr'.symm.trans hs
    exact (congrArg ((a.hom.app M).val.app
      (op ((toProEt T).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))) hb).symm.trans hs'

end AlgebraicGeometry.ProEtale.VaryingRingGraph
