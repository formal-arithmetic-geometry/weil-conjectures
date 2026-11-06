/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaPasting
import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
import WeilConjectures.AlgebraicGeometry.StrictTower.SingleLevelFiniteProperOpenTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerPullbackSquarePasting
import Mathlib.CategoryTheory.Adjunction.Triple
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Normalized proper/open calculus on strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: lem-cbc-strict-tower-proper-open-calculus).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

attribute [local instance] clopenTowerAbelian

set_option backward.isDefEq.respectTransparency false in
private theorem pi_image {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Derived B X) :
    (G B s).map ((pi B s).app M) = (jAdj B s).unit.app ((G B s).obj M) := by
  have hu := jAdj_unit_isIso B s
  let t : Adjunction.Triple (J B s) (G B s) (R B s) := ⟨jAdj B s, adj B s⟩
  let ff := (jAdj B s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have he : openToR B s = t.leftToRight := by
    ext N
    simp [openToR, t, Adjunction.Triple.leftToRight]
  have ho := openToR_isIso B s
  simp only [pi, NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.isIso_inv_app]
  rw [Functor.map_comp]
  apply (cancel_mono ((G B s).map ((openToR B s).app ((G B s).obj M)))).1
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
    Category.comp_id]
  rw [he]
  rw [t.leftToRight_app_obj, Functor.map_comp]
  change _ = (jAdj B s).unit.app _ ≫ (G B s).map ((jAdj B s).counit.app M) ≫ _
  rw [← Category.assoc, (jAdj B s).right_triangle_components]
  exact (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem module_disjoint_direct {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s]
    (hc : Disjoint (Set.range s) (Set.range c)) (N : Modules B C) :
    IsZero ((modulePullback B s).obj ((moduleDirectImage B c).obj N)) := by
  let Uo : X.ProEt := Scheme.ProEt.mk s
  have : IsOpenImmersion Uo.hom := ‹IsOpenImmersion s›
  let A := coefficients B X
  let R₀ := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
  have hz : IsZero ((SheafOfModules.overFunctor R₀ Uo).obj
      ((moduleDirectImage B c).obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let W := (Scheme.proEtaleBaseChange c).obj V.unop.left
    have hsubset : Set.range V.unop.left.hom ⊆ Set.range s := by
      rintro _ ⟨v, rfl⟩
      exact ⟨V.unop.hom.left v,
        congrArg (fun f : V.unop.left.left ⟶ X ↦ f v) V.unop.hom.w⟩
    have hdisj : Disjoint (Set.range V.unop.left.hom) (Set.range c) :=
      hc.mono_left hsubset
    let : IsEmpty W.left := Scheme.isEmpty_pullback V.unop.left.hom c hdisj
    let NN := (SheafOfModules.toSheaf _).obj N
    have hzero := (NN.isTerminalOfBotCover W (Scheme.ProEt.bot_mem_topology W)).isZero
    let : Subsingleton (NN.obj.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero hzero
    change (x : NN.obj.obj (op W)) = 0
    exact @Subsingleton.elim (NN.obj.obj (op W)) inferInstance _ _
  obtain ⟨q, ⟨hq⟩⟩ := Scheme.proEtale_ringed_open_comparison Uo A
  let rc := (sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (constantRingIso B s)
  let e := Scheme.proEtaleScalarEquivalence U rc
  let extAdj := Scheme.proEtaleRingExtensionAdjunction s A (coefficients B U)
    (constantRingIso B s)
  let ee := extAdj.leftAdjointUniq e.symm.toAdjunction
  let t := e.trans q
  let P := Scheme.proEtaleModuleInverseImage s A
  let E := Scheme.proEtaleRingExtension s A (coefficients B U) (constantRingIso B s)
  let hcomp : modulePullback B s ⋙ t.functor ≅ SheafOfModules.overFunctor R₀ Uo :=
    Functor.associator P E (e.functor ⋙ q.functor) ≪≫
      Functor.isoWhiskerLeft P
        ((Functor.associator E e.functor q.functor).symm ≪≫
          Functor.isoWhiskerRight
            (Functor.isoWhiskerRight ee e.functor ≪≫ e.counitIso) q.functor ≪≫
          Functor.leftUnitor q.functor) ≪≫ hq
  have hzero := hz.of_iso (hcomp.app ((moduleDirectImage B c).obj N))
  exact (t.inverse.map_isZero hzero).of_iso (t.unitIso.app _)

set_option backward.isDefEq.respectTransparency false in
private theorem module_disjoint_extension {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Disjoint (Set.range s) (Set.range c)) (N : Modules B U) :
    IsZero ((modulePullback B c).obj ((moduleJ B s).obj N)) := by
  apply (IsZero.iff_id_eq_zero _).2
  let a := Scheme.proEtaleRingModuleAdjunction c (coefficients B X)
    (coefficients B C) (constantRingIso B c)
  apply (a.homEquiv _ _).injective
  apply ((moduleJAdj B s).homEquiv _ _).injective
  exact (module_disjoint_direct B s c hc _).eq_of_tgt _ _
set_option backward.isDefEq.respectTransparency false in
private theorem moduleR_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (N : Modules B X) (U : Y.ProEt)
    (m : ((moduleDirectImage B f).obj N).val.obj (op U)) :
    ((eqToIso (congrArg (moduleDirectImage B) e)).hom.app N).val.app (op U) m =
      N.val.map (eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj U)
        e.symm)).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem moduleRComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    moduleRComp B (𝟙 U) j ≪≫
        eqToIso (congrArg (moduleDirectImage B) (Category.id_comp j)) =
      Functor.isoWhiskerRight (moduleRId B U) (moduleDirectImage B j) ≪≫
        Functor.leftUnitor (moduleDirectImage B j) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  change ((eqToIso (congrArg (moduleDirectImage B) (Category.id_comp j))).hom.app N).val.app
      V (((moduleRComp B (𝟙 U) j).hom.app N).val.app V m) =
    ((moduleRId B U).hom.app N).val.app
      (op ((Scheme.proEtaleBaseChange j).obj V.unop)) m
  rw [moduleR_transport B (Category.id_comp j) N V.unop]
  erw [(Classical.choose_spec (moduleRComp_existsUnique B (𝟙 U) j)).1]
  erw [(Classical.choose_spec (moduleRId_existsUnique B U)).1]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  have hsite :
      eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj V.unop)
        (Category.id_comp j).symm) ≫
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          (𝟙 U) j).hom.app V.unop =
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app
        ((Scheme.proEtaleBaseChange j).obj V.unop) := by
    have hcongr {f g : U ⟶ X} (e : f = g) :
        MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) e =
          eqToIso (congrArg Scheme.proEtaleBaseChange e) := by
      cases e
      simp only [MorphismProperty.Over.pullbackCongr_refl, eqToIso_refl]
    have h := congrArg (fun e ↦ e.hom.app V.unop)
      (MorphismProperty.Over.pullbackComp_id_left
        (P := @WeaklyEtale) (Q := ⊤) j ((𝟙 U) ≫ j) rfl)
    rw [hcongr] at h
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at h
    rw [h]
    simp only [eqToIso.hom,
      eqToHom_refl, NatTrans.id_app, Category.id_comp]
  exact congrArg (fun a : (Scheme.proEtaleBaseChange j).obj V.unop ⟶
      (Scheme.proEtaleBaseChange (𝟙 U)).obj ((Scheme.proEtaleBaseChange j).obj V.unop) ↦
        N.val.map a.op m) hsite

set_option backward.isDefEq.respectTransparency false in
private theorem moduleR_obj_map {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Modules B X)
    {V W : Y.ProEt} (a : V ⟶ W)
    (m : N.val.obj (op ((Scheme.proEtaleBaseChange f).obj W))) :
    ((moduleDirectImage B f).obj N).val.map a.op m =
      N.val.map ((Scheme.proEtaleBaseChange f).map a).op m := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem moduleRComp_id_right {U X : Scheme.{u}} (j : U ⟶ X) :
    moduleRComp B j (𝟙 X) ≪≫
        eqToIso (congrArg (moduleDirectImage B) (Category.comp_id j)) =
      Functor.isoWhiskerLeft (moduleDirectImage B j) (moduleRId B X) ≪≫
        Functor.rightUnitor (moduleDirectImage B j) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  change ((eqToIso (congrArg (moduleDirectImage B) (Category.comp_id j))).hom.app N).val.app
      V (((moduleRComp B j (𝟙 X)).hom.app N).val.app V m) =
    ((moduleRId B X).hom.app ((moduleDirectImage B j).obj N)).val.app V m
  rw [moduleR_transport B (Category.comp_id j) N V.unop]
  erw [(Classical.choose_spec (moduleRComp_existsUnique B j (𝟙 X))).1]
  erw [(Classical.choose_spec (moduleRId_existsUnique B X)).1]
  rw [moduleR_obj_map B j N]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  have hsite :
      eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj V.unop)
        (Category.comp_id j).symm) ≫
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          j (𝟙 X)).hom.app V.unop =
      (Scheme.proEtaleBaseChange j).map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop) := by
    have hcongr {f g : U ⟶ X} (e : f = g) :
        MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) e =
          eqToIso (congrArg Scheme.proEtaleBaseChange e) := by
      cases e
      simp only [MorphismProperty.Over.pullbackCongr_refl, eqToIso_refl]
    have h := congrArg (fun e ↦ e.hom.app V.unop)
      (MorphismProperty.Over.pullbackComp_id_right
        (P := @WeaklyEtale) (Q := ⊤) j (j ≫ (𝟙 X)) rfl)
    rw [hcongr] at h
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at h
    rw [h]
    simp only [eqToIso.hom,
      eqToHom_refl, NatTrans.id_app, Category.id_comp]
  exact congrArg (fun a : (Scheme.proEtaleBaseChange j).obj V.unop ⟶
      (Scheme.proEtaleBaseChange j).obj ((Scheme.proEtaleBaseChange (𝟙 X)).obj V.unop) ↦
        N.val.map a.op m) hsite

section PullbackUnits
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction moduleRComp moduleRId

private theorem leftAdjointCompIso_transport
    {I C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : I → C ⥤ E) (R₀ : I → E ⥤ C) (a : ∀ t, L t ⊣ R₀ t)
    {F : C ⥤ D} {G₀ : D ⥤ E} {F' : D ⥤ C} {G' : E ⥤ D}
    (af : F ⊣ F') (ag : G₀ ⊣ G') {i j : I} (e : i = j)
    (d : G' ⋙ F' ≅ R₀ i) :
    Adjunction.leftAdjointCompIso af ag (a i) d ≪≫ eqToIso (congrArg L e) =
      Adjunction.leftAdjointCompIso af ag (a j) (d ≪≫ eqToIso (congrArg R₀ e)) := by
  cases e
  simp

@[irreducible] private noncomputable def moduleAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback B f ⊣ moduleDirectImage B f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
    (constantRingIso B f)

@[irreducible] private noncomputable def moduleGId (X : Scheme.{u}) :
    modulePullback B (𝟙 X) ≅ 𝟭 (Modules B X) :=
  Adjunction.leftAdjointIdIso
    (Scheme.proEtaleRingModuleAdjunction (𝟙 X) (coefficients B X)
      (coefficients B X) (constantRingIso B (𝟙 X))) (moduleRId B X)

private theorem moduleGComp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleGComp B f g = (Adjunction.leftAdjointCompIso
      (moduleAdj B g) (moduleAdj B f) (moduleAdj B (f ≫ g)) (moduleRComp B f g)).symm := by
  unfold moduleAdj
  rfl

private theorem moduleGId_eq (X : Scheme.{u}) :
    moduleGId B X = Adjunction.leftAdjointIdIso (moduleAdj B (𝟙 X)) (moduleRId B X) := by
  unfold moduleGId moduleAdj
  rfl

private theorem leftAdjoint_unit_left
    {K C D : Type*} [Category* C] [Category* D]
    (L : K → C ⥤ D) (R₀ : K → D ⥤ C) (a : ∀ k, L k ⊣ R₀ k)
    {I S : D ⥤ D} (ai : I ⊣ S) (ri : S ≅ 𝟭 D)
    {i j : K} (e : i = j) (d : S ⋙ R₀ j ≅ R₀ i)
    (hd : d ≪≫ eqToIso (congrArg R₀ e) =
      Functor.isoWhiskerRight ri (R₀ j) ≪≫ Functor.leftUnitor (R₀ j)) :
    (Adjunction.leftAdjointCompIso (a j) ai (a i) d).inv ≫
        Functor.whiskerLeft (L j) (Adjunction.leftAdjointIdIso ai ri).hom =
      (eqToIso (congrArg L e)).hom := by
  have hh := leftAdjointCompIso_transport L R₀ a (a j) ai e d
  rw [hd, Adjunction.leftAdjointCompIso_comp_id _ _ _ _ rfl] at hh
  apply NatTrans.ext
  funext N
  have hN := congrArg (fun q ↦ q.hom.app N) hh
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hN
  let dl := Adjunction.leftAdjointCompIso (a j) ai (a i) d
  have h := congrArg (fun f ↦ dl.inv.app N ≫ f) hN
  dsimp only [dl, Functor.comp_obj, Functor.id_obj] at h
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
    Category.comp_id, NatTrans.comp_app, Functor.whiskerLeft_app] using h.symm

private theorem leftAdjoint_unit_right
    {K C D : Type*} [Category* C] [Category* D]
    (L : K → C ⥤ D) (R₀ : K → D ⥤ C) (a : ∀ k, L k ⊣ R₀ k)
    {I S : C ⥤ C} (ai : I ⊣ S) (ri : S ≅ 𝟭 C)
    {i j : K} (e : i = j) (d : R₀ j ⋙ S ≅ R₀ i)
    (hd : d ≪≫ eqToIso (congrArg R₀ e) =
      Functor.isoWhiskerLeft (R₀ j) ri ≪≫ Functor.rightUnitor (R₀ j)) :
    (Adjunction.leftAdjointCompIso ai (a j) (a i) d).inv ≫
        Functor.whiskerRight (Adjunction.leftAdjointIdIso ai ri).hom (L j) =
      (eqToIso (congrArg L e)).hom := by
  have hh := leftAdjointCompIso_transport L R₀ a ai (a j) e d
  rw [hd, Adjunction.leftAdjointCompIso_id_comp _ _ _ _ rfl] at hh
  apply NatTrans.ext
  funext N
  have hN := congrArg (fun q ↦ q.hom.app N) hh
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hN
  let dl := Adjunction.leftAdjointCompIso ai (a j) (a i) d
  have h := congrArg (fun f ↦ dl.inv.app N ≫ f) hN
  dsimp only [dl, Functor.comp_obj, Functor.id_obj] at h
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
    Category.comp_id, NatTrans.comp_app, Functor.whiskerRight_app] using h.symm

private theorem moduleGComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (moduleGComp B (𝟙 U) j).hom ≫
        Functor.whiskerLeft (modulePullback B j) (moduleGId B U).hom =
      (eqToIso (congrArg (modulePullback B) (Category.id_comp j))).hom := by
  rw [moduleGComp_eq, moduleGId_eq]
  exact leftAdjoint_unit_left (modulePullback B) (moduleDirectImage B) (moduleAdj B)
    (moduleAdj B (𝟙 U)) (moduleRId B U) (Category.id_comp j)
    (moduleRComp B (𝟙 U) j) (moduleRComp_id_left B j)

private theorem moduleGComp_id_right {U X : Scheme.{u}} (j : U ⟶ X) :
    (moduleGComp B j (𝟙 X)).hom ≫
        Functor.whiskerRight (moduleGId B X).hom (modulePullback B j) =
      (eqToIso (congrArg (modulePullback B) (Category.comp_id j))).hom := by
  rw [moduleGComp_eq, moduleGId_eq]
  exact leftAdjoint_unit_right (modulePullback B) (moduleDirectImage B) (moduleAdj B)
    (moduleAdj B (𝟙 X)) (moduleRId B X) (Category.comp_id j)
    (moduleRComp B j (𝟙 X)) (moduleRComp_id_right B j)

@[irreducible] private noncomputable def towerGId (X : Scheme.{u}) :
    towerPullback B (𝟙 X) ≅ 𝟭 (Towers B X) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleGId B X) ≪≫
    Functor.whiskeringRightObjIdIso

attribute [local irreducible] moduleGComp

private theorem whiskering_comp_app
    {C D E K : Type*} [Category* C] [Category* D] [Category* E] [Category* K]
    (F : C ⥤ D) (I : D ⥤ E) (H : C ⥤ E) (a : H ≅ F ⋙ I) (N : K ⥤ C) (n : K) :
    (((Functor.whiskeringRight K C E).mapIso a ≪≫
      Functor.whiskeringRightObjCompIso F I).hom.app N).app n = a.hom.app (N.obj n) := by
  change a.hom.app (N.obj n) ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem whiskering_id_app
    {C E : Type*} [Category* C] [Category* E] (F : C ⥤ C)
    (a : F ≅ 𝟭 C) (N : E ⥤ C) (n : E) :
    (((Functor.whiskeringRight E C C).mapIso a ≪≫
      Functor.whiskeringRightObjIdIso).hom.app N).app n = a.hom.app (N.obj n) := by
  change a.hom.app (N.obj n) ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem towerGComp_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Towers B Z) (n : ℕᵒᵖ) :
    ((towerGComp B f g).hom.app N).app n = (moduleGComp B f g).hom.app (N.obj n) :=
  whiskering_comp_app _ _ _ (moduleGComp B f g) N n

private theorem towerGId_app (X : Scheme.{u}) (N : Towers B X) (n : ℕᵒᵖ) :
    ((towerGId B X).hom.app N).app n = (moduleGId B X).hom.app (N.obj n) := by
  unfold towerGId
  exact whiskering_id_app _ (moduleGId B X) N n

private theorem towerPull_map_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N M : Towers B Y} (a : N ⟶ M) (n : ℕᵒᵖ) :
    ((towerPullback B f).map a).app n = (modulePullback B f).map (a.app n) := rfl

private theorem towerG_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (N : Towers B Y) (n : ℕᵒᵖ) :
    ((eqToIso (congrArg (towerPullback B) e)).hom.app N).app n =
      (eqToIso (congrArg (modulePullback B) e)).hom.app (N.obj n) := by
  cases e
  rfl

private theorem towerGComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (towerGComp B (𝟙 U) j).hom ≫
        Functor.whiskerLeft (towerPullback B j) (towerGId B U).hom =
      (eqToIso (congrArg (towerPullback B) (Category.id_comp j))).hom := by
  apply NatTrans.ext
  funext N
  apply NatTrans.ext
  funext n
  change ((towerGComp B (𝟙 U) j).hom.app N).app n ≫
      ((towerGId B U).hom.app ((towerPullback B j).obj N)).app n =
    ((eqToIso (congrArg (towerPullback B) (Category.id_comp j))).hom.app N).app n
  rw [towerGComp_app, towerGId_app, towerG_transport B (Category.id_comp j)]
  exact congr_app (moduleGComp_id_left B j) (N.obj n)

private theorem towerGComp_id_right {U X : Scheme.{u}} (j : U ⟶ X) :
    (towerGComp B j (𝟙 X)).hom ≫
        Functor.whiskerRight (towerGId B X).hom (towerPullback B j) =
      (eqToIso (congrArg (towerPullback B) (Category.comp_id j))).hom := by
  apply NatTrans.ext
  funext N
  apply NatTrans.ext
  funext n
  change ((towerGComp B j (𝟙 X)).hom.app N).app n ≫
      ((towerPullback B j).map ((towerGId B X).hom.app N)).app n =
    ((eqToIso (congrArg (towerPullback B) (Category.comp_id j))).hom.app N).app n
  rw [towerGComp_app, towerPull_map_app, towerGId_app,
    towerG_transport B (Category.comp_id j)]
  exact congr_app (moduleGComp_id_right B j) (N.obj n)
private theorem derived_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (towerPullback B) e))).hom =
        (eqToIso (congrArg (G B) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem gId_eq (X : Scheme.{u}) :
    gId B X = Functor.mapDerivedCategoryNatIso (towerGId B X) ≪≫
      Functor.mapDerivedCategoryIdIso (Towers B X) := by
  unfold gId towerGId moduleGId
  rfl
attribute [local irreducible] gComp gId towerGComp adj jAdj G R J alpha
private theorem betaInv_id_aux
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {G₀ : D ⥤ C} (a : L ⊣ G₀)
    {I : C ⥤ C} {H : D ⥤ D} (eI : I ≅ 𝟭 C) (eH : H ≅ 𝟭 D)
    (s : H ⋙ G₀ ≅ G₀ ⋙ I)
    (hs : ∀ N, s.inv.app N ≫ G₀.map (eH.hom.app N) = eI.hom.app (G₀.obj N))
    (M : C) :
    (a.homEquiv _ _).symm (I.map (a.unit.app M) ≫ s.inv.app (L.obj M)) ≫
        eH.hom.app (L.obj M) = L.map (eI.hom.app M) := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Category.assoc, hs, Adjunction.homEquiv_unit]
  exact (eI.hom.naturality (a.unit.app M)).trans (a.unit.naturality (eI.hom.app M))
private theorem squareG_flip {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    squareG B r k i p h.symm = (squareG B k r p i h).symm := by
  simp only [squareG, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

private theorem leftAdjointIdIso_transpose
    {C : Type*} [Category* C] {L G₀ : C ⥤ C} (a : L ⊣ G₀)
    (e : G₀ ≅ 𝟭 C) (N : C) :
    a.unit.app N ≫ G₀.map ((Adjunction.leftAdjointIdIso a e).hom.app N) =
      e.inv.app N := by
  have h := unit_conjugateEquiv Adjunction.id a (Adjunction.leftAdjointIdIso a e).hom N
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  simpa only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp]
    using h.symm

private theorem jId_transpose (X : Scheme.{u}) (N : Derived B X) :
    (jAdj B (𝟙 X)).unit.app N ≫
        (G B (𝟙 X)).map ((jId B X).hom.app N) = (gId B X).inv.app N := by
  exact leftAdjointIdIso_transpose (jAdj B (𝟙 X)) (gId B X) N
private theorem betaInv_id_open_aux
    {C D : Type*} [Category* C] [Category* D]
    {J₀ G₀ : C ⥤ C} {J₁ G₁ : D ⥤ D} (a₀ : J₀ ⊣ G₀) (a₁ : J₁ ⊣ G₁)
    (F : C ⥤ D) (e₀ : G₀ ≅ 𝟭 C) (e₁ : G₁ ≅ 𝟭 D)
    (j₀ : J₀ ≅ 𝟭 C) (j₁ : J₁ ≅ 𝟭 D) (s : F ⋙ G₁ ≅ G₀ ⋙ F)
    (h₀ : ∀ N, a₀.unit.app N ≫ G₀.map (j₀.hom.app N) = e₀.inv.app N)
    (h₁ : ∀ N, a₁.unit.app N ≫ G₁.map (j₁.hom.app N) = e₁.inv.app N)
    (hs : ∀ N, s.inv.app N ≫ e₁.hom.app (F.obj N) = F.map (e₀.hom.app N))
    (N : C) :
    (a₁.homEquiv _ _).symm (F.map (a₀.unit.app N) ≫ s.inv.app (J₀.obj N)) ≫
        F.map (j₀.hom.app N) = j₁.hom.app (F.obj N) := by
  apply (a₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  dsimp only [Functor.id_obj]
  rw [h₁]
  have hn := s.inv.naturality (j₀.hom.app N)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, h₀]
  apply (cancel_mono (e₁.hom.app (F.obj N))).1
  rw [Category.assoc, hs, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (F.map_id _).trans (Iso.inv_hom_id_app e₁ _).symm
private theorem iso_unit_cancel {C : Type*} [Category* C] {X Y Z : C}
    (e : X ≅ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (h : e.inv ≫ a = b) : e.hom ≫ b = a := by
  rw [← h, ← Category.assoc, e.hom_inv_id, Category.id_comp]
private theorem betaInv_mate {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g) :
    mateEquiv (jAdj B j) (jAdj B j') (betaInv B a j' j g w) =
      (squareG B a j' j g w).inv := by
  apply mateEquiv_eq_of_unit
  intro M
  symm
  change (jAdj B j').homEquiv _ _ (betaInvApp B a j' j g w M) = _
  exact ((jAdj B j').homEquiv _ _).apply_symm_apply _

private theorem jComp_conjugate {U V X : Scheme.{u}} (k : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    conjugateEquiv (jAdj B (k ≫ j)) ((jAdj B k).comp (jAdj B j))
      (jComp B k j).hom = (gComp B k j).hom := by
  simp [jComp, Adjunction.leftAdjointCompIso, conjugateIsoEquiv]

private theorem betaInv_open_comp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (hp : ∀ N : Derived B X,
      (G B b).map ((gComp B k j).hom.app N) ≫
        (squareG B b k₁ k a wk).inv.app ((G B j).obj N) ≫
        (G B k₁).map ((squareG B a j₁ j g wj).inv.app N) =
      (squareG B b (k₁ ≫ j₁) (k ≫ j) g w).inv.app N ≫
        (gComp B k₁ j₁).hom.app ((G B g).obj N)) :
    betaInv B b (k₁ ≫ j₁) (k ≫ j) g w =
      (((TwoSquare.mk _ _ _ _ (betaInv B b k₁ k a wk)).vComp
        (TwoSquare.mk _ _ _ _ (betaInv B a j₁ j g wj))).whiskerLeft
          (jComp B k j).hom).whiskerRight (jComp B k₁ j₁).inv := by
  apply (mateEquiv (jAdj B (k ≫ j)) (jAdj B (k₁ ≫ j₁))).injective
  rw [betaInv_mate, mateEquiv_conjugateEquiv_vcomp _
    ((jAdj B k₁).comp (jAdj B j₁)),
    conjugateEquiv_mateEquiv_vcomp _ ((jAdj B k).comp (jAdj B j)),
    mateEquiv_hcomp, betaInv_mate, betaInv_mate, jComp_conjugate]
  rw [show conjugateEquiv ((jAdj B k₁).comp (jAdj B j₁)) (jAdj B (k₁ ≫ j₁))
    (jComp B k₁ j₁).inv = (gComp B k₁ j₁).inv from
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _]
  ext N
  dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  set_option backward.isDefEq.respectTransparency false in
    change _ = ((G B b).map ((gComp B k j).hom.app N) ≫
    ((squareG B b k₁ k a wk).inv.app ((G B j).obj N) ≫
      (G B k₁).map ((squareG B a j₁ j g wj).inv.app N))) ≫
        (gComp B k₁ j₁).inv.app ((G B g).obj N)
  rw [hp N]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm
end PullbackUnits

section NormalizedIdentities
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] gComp gId adj jAdj G R J alpha
private theorem betaInv_unit {A A' Y Y' : Scheme.{u}}
    (a : A' ⟶ A) (j' : A' ⟶ Y') (j : A ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (M : Derived B A) :
    (jAdj B j').unit.app ((G B a).obj M) ≫
        (G B j').map ((betaInv B a j' j g w).app M) =
      (G B a).map ((jAdj B j).unit.app M) ≫
        (squareG B a j' j g w).inv.app ((J B j).obj M) := by
  change (jAdj B j').homEquiv _ _ (betaInvApp B a j' j g w M) = _
  exact ((jAdj B j').homEquiv _ _).apply_symm_apply _

end NormalizedIdentities
/-- Select the second witness without repeatedly expanding a large normalization
predicate in the kernel. This is precisely the nested choice used by the finite
proper/open coherence theorem, not a new choice of unnormalized comparison.
Source: Stacks, Tag 0F7B and the finite coherence interface
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
noncomputable def secondWitness {A : Sort v} {C : Sort w} {P : A → C → Prop}
    (h : ∃ a c, P a c) : C :=
  h.choose_spec.choose

/-- The finite etale comparison furnished by the dependency's section and derived-unit
normalizations; these determine its arrow, including the refinement case.
Source: Stacks, Tag 0F7B
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
@[no_expose] noncomputable def finiteGamma (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p :=
  secondWitness (Etale.properOpenInterchangeCoherence Λ) k i r p h

/-- The canonical identification of the evaluated source with the finite etale
source, retaining the evaluation mates and the specified origin isomorphism.
Source: blueprint, seventh and eighth proof steps
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
noncomputable def finiteSource {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T)
    [IsProper r] [IsOpenImmersion i] (M : Derived B V) (n : ℕ)
    (w : ScalarEtaleOrigin B V ((ev B V n).obj M)) :
    (HD B T w.Λ w.φ).obj
        (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} w.Λ) i).mapDerivedCategoryPlus).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} w.Λ) r).obj w.origin.L)) ≅
      (ev B T n).obj ((J B i).obj ((R B r).obj M)) :=
  (hJ B i w.Λ w.φ).app _ ≪≫
  (moduleJ B i).mapDerivedCategory.mapIso
    ((@asIso _ _ _ _ (hR B r w.Λ w.φ) (hR_isIso B r w.Λ w.φ)).app w.origin.L) ≪≫
  (moduleJ B i).mapDerivedCategory.mapIso
    ((moduleDirectImage B r).rightDerivedFunctor.mapIso (originIso B w)) ≪≫
  (moduleJ B i).mapDerivedCategory.mapIso
    ((@asIso _ _ _ _ (evalR B r n) (evalR_isIso B r n)).app M).symm ≪≫
  (evalJ B i n).symm.app ((R B r).obj M)

/-- The canonical identification of the evaluated target with the finite etale
target, using the same comparisons and origin. Source: blueprint, steps 7--8
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
noncomputable def finiteTarget {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion k] [IsProper p] (M : Derived B V) (n : ℕ)
    (w : ScalarEtaleOrigin B V ((ev B V n).obj M)) :
    (HD B T w.Λ w.φ).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} w.Λ) p).obj
          (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} w.Λ) k).mapDerivedCategoryPlus).obj
            w.origin.L)) ≅
      (ev B T n).obj ((R B p).obj ((J B k).obj M)) :=
  (@asIso _ _ _ _ (hR B p w.Λ w.φ) (hR_isIso B p w.Λ w.φ)).app _ ≪≫
  (moduleDirectImage B p).rightDerivedFunctor.mapIso ((hJ B k w.Λ w.φ).app w.origin.L) ≪≫
  (moduleDirectImage B p).rightDerivedFunctor.mapIso
    ((moduleJ B k).mapDerivedCategory.mapIso (originIso B w)) ≪≫
  (moduleDirectImage B p).rightDerivedFunctor.mapIso ((evalJ B k n).symm.app M) ≪≫
  ((@asIso _ _ _ _ (evalR B p n) (evalR_isIso B p n)).app ((J B k).obj M)).symm

attribute [local irreducible] finiteSource finiteTarget

private theorem isIso_of_evaluations
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] {M N : DerivedCategory (ℕᵒᵖ ⥤ C)} (f : M ⟶ N)
    (hf : ∀ n : ℕᵒᵖ, IsIso (((evaluation ℕᵒᵖ C).obj n).mapDerivedCategory.map f)) :
    IsIso f := by
  apply (DerivedCategory.isIso_iff _ f).2
  intro q
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  have := hf n
  exact (NatIso.isIso_map_iff
    (((evaluation ℕᵒᵖ C).obj n).mapDerivedCategoryHomologyFunctorIso q) f).2 (by
      change IsIso ((DerivedCategory.homologyFunctor C q).map
        (((evaluation ℕᵒᵖ C).obj n).mapDerivedCategory.map f))
      infer_instance)
section GammaIdentities
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] adj jAdj G R J alpha gComp gId jId

private theorem mate_whisker
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : G ⋙ L₂ ⟶ L₁ ⋙ H) (t : G' ⟶ G) (b : H ⟶ H') :
    mateEquiv adj₁ adj₂
        (Functor.whiskerRight t L₂ ≫ a ≫ Functor.whiskerLeft L₁ b) =
      Functor.whiskerLeft R₁ t ≫ mateEquiv adj₁ adj₂ a ≫
        Functor.whiskerRight b R₂ := by
  apply TwoSquare.ext
  intro X
  dsimp [mateEquiv, TwoSquare.natTrans]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have ht := adj₂.unit.naturality (t.app (R₁.obj X))
  dsimp at ht
  rw [← reassoc_of% ht]
  slice_lhs 4 5 => rw [← R₂.map_comp, ← b.naturality, R₂.map_comp]

private theorem mate_identity_vertical
    {C D : Type*} [Category* C] [Category* D]
    {L₀ R₀ : C ⥤ C} {L₁ R₁ : D ⥤ D} (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁)
    (e₀ : L₀ ≅ 𝟭 C) (e₁ : L₁ ≅ 𝟭 D) (F : C ⥤ D)
    (a : F ⋙ L₁ ⟶ L₀ ⋙ F)
    (ha : ∀ N, a.app N ≫ F.map (e₀.hom.app N) = e₁.hom.app (F.obj N)) (M : C) :
    (mateEquiv adj₀ adj₁ a).app M ≫
        ((conjugateIsoEquiv Adjunction.id adj₁ e₁).symm).hom.app (F.obj M) =
      F.map (((conjugateIsoEquiv Adjunction.id adj₀ e₀).symm).hom.app M) := by
  let A := TwoSquare.mk _ _ _ _ a
  have hA : A.whiskerLeft e₀.hom = (TwoSquare.vId F).whiskerRight e₁.hom := by
    apply TwoSquare.ext
    intro N
    dsimp [A, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vId]
    simpa only [TwoSquare.mk, TwoSquare.natTrans, Category.comp_id, Category.id_comp]
      using ha N
  have hm := mateEquiv_whiskerTop_conjugateEquiv
    Adjunction.id adj₀ Adjunction.id adj₁ e₀.hom e₁.hom (TwoSquare.vId F) A hA
  have hmM := congrArg (fun t ↦ t.app M) hm
  have hi : mateEquiv Adjunction.id Adjunction.id (TwoSquare.vId F) =
      TwoSquare.hId F := by
    apply TwoSquare.ext
    intro N
    simp [mateEquiv, TwoSquare.vId, TwoSquare.hId, Adjunction.id]
  rw [hi] at hmM
  have hh : F.map ((conjugateIsoEquiv Adjunction.id adj₀ e₀).hom.app M) ≫
      (mateEquiv adj₀ adj₁ a).app M =
        (conjugateIsoEquiv Adjunction.id adj₁ e₁).hom.app (F.obj M) := by
    simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.hId_app, A, TwoSquare.mk, TwoSquare.natTrans] at hmM
    dsimp only [Functor.id_obj] at hmM
    erw [Category.id_comp] at hmM
    simpa only [conjugateIsoEquiv_apply_hom] using hmM
  have hh' := congrArg (fun f ↦
    F.map ((conjugateIsoEquiv Adjunction.id adj₀ e₀).inv.app M) ≫ f ≫
      (conjugateIsoEquiv Adjunction.id adj₁ e₁).inv.app (F.obj M)) hh
  simpa only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Functor.id_obj,
    Category.id_comp, Category.comp_id, Iso.symm_hom] using hh'

private theorem mate_identity_horizontal
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R₀ : D ⥤ C} (adj₀ : L ⊣ R₀)
    (I₀ : C ⥤ C) (I₁ : D ⥤ D) (e₀ : I₀ ≅ 𝟭 C) (e₁ : I₁ ≅ 𝟭 D)
    (a : I₀ ⋙ L ⟶ L ⋙ I₁)
    (ha : ∀ N, a.app N ≫ e₁.hom.app (L.obj N) = L.map (e₀.hom.app N)) (M : D) :
    (mateEquiv adj₀ adj₀ a).app M ≫ R₀.map (e₁.hom.app M) =
      e₀.hom.app (R₀.obj M) := by
  let A := TwoSquare.mk _ _ _ _ a
  have hA : (A.whiskerTop e₀.inv).whiskerBottom e₁.hom = TwoSquare.hId L := by
    apply TwoSquare.ext
    intro N
    dsimp [A, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hId]
    have hh := congrArg (fun f ↦ L.map (e₀.inv.app N) ≫ f) (ha N)
    simpa [TwoSquare.mk, TwoSquare.natTrans, ← Functor.map_comp,
      Category.assoc] using hh
  have hm := congrArg (mateEquiv adj₀ adj₀) hA
  simp only [A, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.natTrans, TwoSquare.mk, Category.assoc] at hm
  rw [mate_whisker] at hm
  have hmM := congrArg (fun t ↦ t.app M) hm
  have hh : e₀.inv.app (R₀.obj M) ≫ (mateEquiv adj₀ adj₀ a).app M ≫
      R₀.map (e₁.hom.app M) = 𝟙 _ := by
    simpa [A, TwoSquare.hId, mateEquiv] using hmM
  have hh' := congrArg (fun f ↦ e₀.hom.app (R₀.obj M) ≫ f) hh
  simpa only [← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp, Category.comp_id] using hh'
end GammaIdentities

end AlgebraicGeometry.ProEtale.StrictTower
