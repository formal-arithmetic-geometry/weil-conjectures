/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
public import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.StrictTowerPullbackSquarePasting
import Sheaf.AlgebraicGeometry.StrictTowerGammaEvaluation
import Sheaf.AlgebraicGeometry.SingleProperOpenFiniteNormalization
import Mathlib.CategoryTheory.Adjunction.Triple
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
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
private theorem derived_disjoint_extension {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Disjoint (Set.range s) (Set.range c)) (N : Derived B U) :
    IsZero ((G B c).obj ((J B s).obj N)) := by
  let F := towerJ B s ⋙ towerPullback B c
  have hzero (M : Towers B U) : IsZero (F.obj M) := by
    apply (Functor.isZero_iff _).2
    intro n
    exact module_disjoint_extension B s c hc (M.obj n)
  have hz := F.isZero_mapDerivedCategory_obj N (fun q ↦ hzero _)
  exact hz.of_iso ((Functor.mapDerivedCategoryCompIso (towerJ B s)
    (towerPullback B c)).app N).symm

/-- The clopen projection is identity on the image and zero on the complementary open.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: split each test object into the inverse image of the two open components.
The sheaf condition is the product decomposition. The direct-image adjunction unit
is projection to the image component, and the inverse open-to-direct comparison
identifies that component with extension by zero. This is natural in modules,
transitions and differentials; exact localization preserves both equations. -/
theorem pi_components {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Derived B X) :
    (G B s).map ((pi B s).app M) = (jAdj B s).unit.app ((G B s).obj M) ∧
      (G B c).map ((pi B s).app M) = 0 := by
  refine ⟨pi_image B s M, ?_⟩
  have hc' : Disjoint (Set.range s) (Set.range c) := by
    rw [hc]
    exact disjoint_compl_right
  exact (derived_disjoint_extension B s c hc' ((G B s).obj M)).eq_of_tgt _ _

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

private theorem derived_unit_left
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F H : C ⥤ D) (I : D ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (a : H ≅ F ⋙ I) (e : I ≅ 𝟭 D) (b : H ≅ F)
    (ha : a.hom ≫ Functor.whiskerLeft F e.hom = b.hom) :
    (Functor.mapDerivedCategoryNatIso a).hom ≫
        (Functor.mapDerivedCategoryCompIso F I).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          ((Functor.mapDerivedCategoryNatIso e).hom ≫
            (Functor.mapDerivedCategoryIdIso D).hom) =
      (Functor.mapDerivedCategoryNatIso b).hom := by
  have he : a ≪≫ Functor.isoWhiskerLeft F e = b := Iso.ext ha
  have h := congrArg (fun c ↦ (Functor.mapDerivedCategoryNatIso c).hom) he
  rw [Functor.mapDerivedCategoryNatIso_trans] at h
  have hn := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e
  have hu := Functor.mapDerivedCategoryCompIso_comp_id F
  apply NatTrans.ext
  funext N
  have hN := congr_app h N
  have hnN := congr_app hn N
  have huN := congr_app hu N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at *
  rw [← reassoc_of% hnN, huN]
  erw [Category.comp_id]
  exact hN


private theorem derived_unit_right
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F H : C ⥤ D) (I : C ⥤ C)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (a : H ≅ I ⋙ F) (e : I ≅ 𝟭 C) (b : H ≅ F)
    (ha : a.hom ≫ Functor.whiskerRight e.hom F = b.hom) :
    (Functor.mapDerivedCategoryNatIso a).hom ≫
        (Functor.mapDerivedCategoryCompIso I F).hom ≫
        Functor.whiskerRight
          ((Functor.mapDerivedCategoryNatIso e).hom ≫
            (Functor.mapDerivedCategoryIdIso C).hom) F.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso b).hom := by
  have he : a ≪≫ Functor.isoWhiskerRight e F = b := Iso.ext ha
  have h := congrArg (fun c ↦ (Functor.mapDerivedCategoryNatIso c).hom) he
  rw [Functor.mapDerivedCategoryNatIso_trans] at h
  have hn := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F
  have hu := Functor.mapDerivedCategoryCompIso_id_comp F
  apply NatTrans.ext
  funext N
  have hN := congr_app h N
  have hnN := congr_app hn N
  have huN := congr_app hu N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app,
    Functor.map_comp] at *
  rw [← reassoc_of% hnN, huN]
  erw [Category.comp_id]
  exact hN

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

private theorem gComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (gComp B f g).hom = (Functor.mapDerivedCategoryNatIso (towerGComp B f g)).hom ≫
      (Functor.mapDerivedCategoryCompIso (towerPullback B g) (towerPullback B f)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem gComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (gComp B (𝟙 U) j).hom ≫
        Functor.whiskerLeft (G B j) (gId B U).hom =
      (eqToIso (congrArg (G B) (Category.id_comp j))).hom := by
  dsimp only [G]
  rw [gId_eq, gComp_hom]
  change (_ ≫ _) ≫ Functor.whiskerLeft (towerPullback B j).mapDerivedCategory
    ((Functor.mapDerivedCategoryNatIso (towerGId B U)).hom ≫
      (Functor.mapDerivedCategoryIdIso (Towers B U)).hom) = _
  rw [Category.assoc]
  exact
    (derived_unit_left (towerPullback B j) (towerPullback B ((𝟙 U) ≫ j))
    (towerPullback B (𝟙 U)) (towerGComp B (𝟙 U) j) (towerGId B U)
    (eqToIso (congrArg (towerPullback B) (Category.id_comp j)))
    (towerGComp_id_left B j)).trans (derived_transport B (Category.id_comp j))

set_option backward.isDefEq.respectTransparency.types false in
private theorem gComp_id_right {U X : Scheme.{u}} (j : U ⟶ X) :
    (gComp B j (𝟙 X)).hom ≫
        Functor.whiskerRight (gId B X).hom (G B j) =
      (eqToIso (congrArg (G B) (Category.comp_id j))).hom := by
  dsimp only [G]
  rw [gId_eq, gComp_hom]
  change (_ ≫ _) ≫ Functor.whiskerRight
    ((Functor.mapDerivedCategoryNatIso (towerGId B X)).hom ≫
      (Functor.mapDerivedCategoryIdIso (Towers B X)).hom)
    (towerPullback B j).mapDerivedCategory = _
  rw [Category.assoc]
  exact
    (derived_unit_right (towerPullback B j) (towerPullback B (j ≫ (𝟙 X)))
    (towerPullback B (𝟙 X)) (towerGComp B j (𝟙 X)) (towerGId B X)
    (eqToIso (congrArg (towerPullback B) (Category.comp_id j)))
    (towerGComp_id_right B j)).trans (derived_transport B (Category.comp_id j))


attribute [local irreducible] gComp gId towerGComp adj jAdj G R J alpha

private theorem squareG_id {U X : Scheme.{u}} (j : U ⟶ X)
    (h : (𝟙 U) ≫ j = j ≫ (𝟙 X)) (N : Derived B X) :
    (squareG B (𝟙 U) j j (𝟙 X) h).inv.app N ≫
        (G B j).map ((gId B X).hom.app N) =
      (gId B U).hom.app ((G B j).obj N) := by
  have hl := congr_app (gComp_id_left B j) N
  have hr := congr_app (gComp_id_right B j) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hl hr
  have ht : (eqToIso (congrArg (G B) h)).hom ≫
      (eqToIso (congrArg (G B) (Category.comp_id j))).hom =
        (eqToIso (congrArg (G B) (Category.id_comp j))).hom := by
    simp only [eqToIso.hom, eqToHom_trans]
  have htN := congr_app ht N
  simp only [NatTrans.comp_app] at htN
  simp only [squareG, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    eqToIso.inv, Category.assoc]
  change (gComp B (𝟙 U) j).inv.app N ≫
      (eqToIso (congrArg (G B) h)).hom.app N ≫
      (gComp B j (𝟙 X)).hom.app N ≫
      (G B j).map ((gId B X).hom.app N) = _
  rw [hr, htN, ← hl]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

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

private theorem betaInv_id {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : (𝟙 U) ≫ j = j ≫ (𝟙 X)) (M : Derived B U) :
    (betaInv B (𝟙 U) j j (𝟙 X) h).app M ≫
        (gId B X).hom.app ((J B j).obj M) =
      (J B j).map ((gId B U).hom.app M) := by
  exact betaInv_id_aux (jAdj B j) (gId B U) (gId B X)
    (squareG B (𝟙 U) j j (𝟙 X) h) (squareG_id B j h) M

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

private theorem squareG_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (N : Derived B X) :
    (squareG B p (𝟙 U) (𝟙 X) p h).inv.app N ≫
        (gId B U).hom.app ((G B p).obj N) =
      (G B p).map ((gId B X).hom.app N) := by
  rw [squareG_flip B (𝟙 U) p p (𝟙 X) h.symm, Iso.symm_inv]
  apply (cancel_epi ((squareG B (𝟙 U) p p (𝟙 X) h.symm).inv.app N)).1
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact (squareG_id B p h.symm N).symm

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

private theorem betaInv_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (N : Derived B X) :
    (betaInv B p (𝟙 U) (𝟙 X) p h).app N ≫
        (G B p).map ((jId B X).hom.app N) =
      (jId B U).hom.app ((G B p).obj N) := by
  exact betaInv_id_open_aux (jAdj B (𝟙 X)) (jAdj B (𝟙 U)) (G B p)
    (gId B X) (gId B U) (jId B X) (jId B U)
    (squareG B p (𝟙 U) (𝟙 X) p h) (jId_transpose B X) (jId_transpose B U)
    (squareG_id_open B p h) N

private theorem iso_unit_cancel {C : Type*} [Category* C] {X Y Z : C}
    (e : X ≅ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (h : e.inv ≫ a = b) : e.hom ≫ b = a := by
  rw [← h, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem beta_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (hsq : IsPullback p (𝟙 U) (𝟙 X) p)
    (N : Derived B X) :
    (beta B p (𝟙 U) (𝟙 X) p h hsq).hom.app N ≫
        (jId B U).hom.app ((G B p).obj N) =
      (G B p).map ((jId B X).hom.app N) := by
  exact iso_unit_cancel ((beta B p (𝟙 U) (𝟙 X) p h hsq).app N) _ _
    (betaInv_id_open B p h N)

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

set_option backward.isDefEq.respectTransparency false in
private theorem beta_open_comp_aux {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (sk : IsPullback b k₁ k a) (sj : IsPullback a j₁ j g)
    (s : IsPullback b (k₁ ≫ j₁) (k ≫ j) g) (M : Derived B V) :
    (G B g).map ((jComp B k j).inv.app M) ≫
        (beta B a j₁ j g wj sj).hom.app ((J B k).obj M) ≫
        (J B j₁).map ((beta B b k₁ k a wk sk).hom.app M) ≫
        (jComp B k₁ j₁).hom.app ((G B b).obj M) =
      (beta B b (k₁ ≫ j₁) (k ≫ j) g w s).hom.app M := by
  have hp (N : Derived B X) :
      (G B b).map ((gComp B k j).hom.app N) ≫
        (squareG B b k₁ k a wk).inv.app ((G B j).obj N) ≫
        (G B k₁).map ((squareG B a j₁ j g wj).inv.app N) =
      (squareG B b (k₁ ≫ j₁) (k ≫ j) g w).inv.app N ≫
        (gComp B k₁ j₁).hom.app ((G B g).obj N) := by
    have hh := squareG_pasting_inv B g a b j k j₁ k₁
      wj.symm wk.symm w.symm N
    rw [squareG_flip B a j₁ j g wj, squareG_flip B b k₁ k a wk,
      squareG_flip B b (k₁ ≫ j₁) (k ≫ j) g w] at hh
    simp only [Iso.symm_inv] at hh
    apply (cancel_epi ((squareG B b (k₁ ≫ j₁) (k ≫ j) g w).hom.app N)).1
    rw [← Category.assoc, ← hh]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [(G B k₁).map_id, Category.comp_id]
  have hi := congr_app (betaInv_open_comp B k j k₁ j₁ a b g wk wj w hp) M
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk, TwoSquare.natTrans] at hi
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hi
  let e := beta B b (k₁ ≫ j₁) (k ≫ j) g w s
  let e₁ := beta B b k₁ k a wk sk
  let e₂ := beta B a j₁ j g wj sj
  change _ = e.hom.app M
  apply (cancel_epi (e.inv.app M)).1
  change (betaInv B b (k₁ ≫ j₁) (k ≫ j) g w).app M ≫ _ = _
  rw [hi]
  simp only [Category.assoc]
  change (jComp B k₁ j₁).inv.app _ ≫ (J B j₁).map (e₁.inv.app M) ≫
    e₂.inv.app ((J B k).obj M) ≫ (G B g).map ((jComp B k j).hom.app M) ≫
      (G B g).map ((jComp B k j).inv.app M) ≫ e₂.hom.app _ ≫
        (J B j₁).map (e₁.hom.app M) ≫ (jComp B k₁ j₁).hom.app _ = _
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app]
  erw [(G B g).map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(J B j₁).map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

end PullbackUnits

section NormalizedIdentities
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] gComp gId adj jAdj G R J alpha

/-- Beta is normalized to identity on an identity base change.
Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: transpose the two maps under the open adjunction. The unit equation of the
identity inverse-image compositor makes both transposes the open unit. -/
theorem beta_id {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : (𝟙 U) ≫ j = j ≫ (𝟙 X)) (hsq : IsPullback (𝟙 U) j j (𝟙 X))
    (M : Derived B U) :
    (beta B (𝟙 U) j j (𝟙 X) h hsq).hom.app M ≫
        (J B j).map ((gId B U).hom.app M) = (gId B X).hom.app ((J B j).obj M) := by
  have he : (betaInv B (𝟙 U) j j (𝟙 X) h) ≫
      Functor.whiskerLeft (J B j) (gId B X).hom =
        Functor.whiskerRight (gId B U).hom (J B j) := by
    apply NatTrans.ext
    funext N
    exact betaInv_id B j h N
  exact congr_app (iso_unit_cancel (beta B (𝟙 U) j j (𝟙 X) h hsq) _ _ he) M


end NormalizedIdentities

private theorem transposed_pasting
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {A : C₀ ⥤ C₁} {B : C₁ ⥤ C₂} {C : C₀ ⥤ C₂}
    {F : D₀ ⥤ D₁} {H : D₁ ⥤ D₂} {K : D₀ ⥤ D₂}
    (c : C ⟶ A ⋙ B) (d : K ⟶ F ⋙ H)
    (t₁ : R₀ ⋙ A ⟶ F ⋙ R₁) (t₂ : R₁ ⋙ B ⟶ H ⋙ R₂)
    (t : R₀ ⋙ C ⟶ K ⋙ R₂)
    (v₁ : A ⋙ L₁ ⟶ L₀ ⋙ F) (v₂ : B ⋙ L₂ ⟶ L₁ ⋙ H)
    (v : C ⋙ L₂ ⟶ L₀ ⋙ K)
    (h₁ : ∀ M, a₁.unit.app (A.obj M) ≫ R₁.map (v₁.app M) =
      A.map (a₀.unit.app M) ≫ t₁.app (L₀.obj M))
    (h₂ : ∀ M, a₂.unit.app (B.obj M) ≫ R₂.map (v₂.app M) =
      B.map (a₁.unit.app M) ≫ t₂.app (L₁.obj M))
    (hv : ∀ M, a₂.unit.app (C.obj M) ≫ R₂.map (v.app M) =
      C.map (a₀.unit.app M) ≫ t.app (L₀.obj M))
    (ht : ∀ N, c.app (R₀.obj N) ≫ B.map (t₁.app N) ≫ t₂.app (F.obj N) =
      t.app N ≫ R₂.map (d.app N)) (M : C₀) :
    L₂.map (c.app M) ≫ v₂.app (A.obj M) ≫ H.map (v₁.app M) =
      v.app M ≫ d.app (L₀.obj M) := by
  apply (a₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← reassoc_of% (a₂.unit.naturality (c.app M))]
  rw [reassoc_of% (h₂ (A.obj M)), reassoc_of% (hv M)]
  erw [← t₂.naturality (v₁.app M)]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [← Category.assoc (B.map _), ← B.map_comp, h₁ M, B.map_comp]
  rw [Category.assoc, ← reassoc_of% (c.naturality (a₀.unit.app M))]
  rw [ht]

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
/-- Successive base changes of beta agree with the composite, before evaluation.
Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: transpose both inverse comparisons under the final open adjunction. Both are
the same iterated pullback of the original open unit; unit naturality identifies the
successive transpose. Injectivity of the adjunction Hom equivalence gives equality. -/
theorem beta_comp {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    [IsOpenImmersion j] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g))
    (s₁ : IsPullback a j₁ j g) (s₂ : IsPullback b j₂ j₁ h)
    (s : IsPullback (b ≫ a) j₂ j (h ≫ g)) (M : Derived B U) :
    (gComp B h g).hom.app ((J B j).obj M) ≫
        (G B h).map ((beta B a j₁ j g w₁ s₁).hom.app M) ≫
        (beta B b j₂ j₁ h w₂ s₂).hom.app ((G B a).obj M) =
      (beta B (b ≫ a) j₂ j (h ≫ g) w s).hom.app M ≫
        (J B j₂).map ((gComp B b a).hom.app M) := by
  let e₁ := beta B a j₁ j g w₁ s₁
  let e₂ := beta B b j₂ j₁ h w₂ s₂
  let e := beta B (b ≫ a) j₂ j (h ≫ g) w s
  have hInv : (J B j₂).map ((gComp B b a).hom.app M) ≫
      e₂.inv.app ((G B a).obj M) ≫ (G B h).map (e₁.inv.app M) =
        e.inv.app M ≫ (gComp B h g).hom.app ((J B j).obj M) := by
    exact transposed_pasting (jAdj B j) (jAdj B j₁) (jAdj B j₂)
      (gComp B b a).hom (gComp B h g).hom
      (squareG B a j₁ j g w₁).inv (squareG B b j₂ j₁ h w₂).inv
      (squareG B (b ≫ a) j₂ j (h ≫ g) w).inv
      (betaInv B a j₁ j g w₁) (betaInv B b j₂ j₁ h w₂)
      (betaInv B (b ≫ a) j₂ j (h ≫ g) w)
      (betaInv_unit B a j₁ j g w₁) (betaInv_unit B b j₂ j₁ h w₂)
      (betaInv_unit B (b ≫ a) j₂ j (h ≫ g) w)
      (squareG_pasting_inv B j j₁ j₂ g h a b w₁ w₂ w) M
  change _ ≫ (G B h).map (e₁.hom.app M) ≫ e₂.hom.app _ =
    e.hom.app M ≫ _
  apply (cancel_epi (e.inv.app M)).1
  rw [← Category.assoc, ← Category.assoc, ← hInv]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(G B h).map_id]
  erw [Category.id_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]


/-- Beta commutes with composition of open immersions, before evaluation.
Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: transpose under the composite open adjunction. Its unit is the composite of
the two open units, so naturality and the normalized pullback compositors identify
the two transposes. Injectivity of the Hom equivalence gives the stated equality. -/
theorem beta_open_comp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (sk : IsPullback b k₁ k a) (sj : IsPullback a j₁ j g)
    (s : IsPullback b (k₁ ≫ j₁) (k ≫ j) g) (M : Derived B V) :
    (G B g).map ((jComp B k j).inv.app M) ≫
        (beta B a j₁ j g wj sj).hom.app ((J B k).obj M) ≫
        (J B j₁).map ((beta B b k₁ k a wk sk).hom.app M) ≫
        (jComp B k₁ j₁).hom.app ((G B b).obj M) =
      (beta B b (k₁ ≫ j₁) (k ≫ j) g w s).hom.app M := by
  exact beta_open_comp_aux B k j k₁ j₁ a b g wk wj w sk sj s M

section CartesianNormalization
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] G R J gComp gId jAdj adj jComp jCongr pi alpha
  towers_hasDerivedCategory

private theorem clopen_map_injective {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] {M : Derived B X} {N : Derived B U}
    {f g : M ⟶ (J B s).obj N} (h : (G B s).map f = (G B s).map g) : f = g := by
  have := openToR_isIso B s
  apply (cancel_mono ((openToR B s).app N)).1
  apply ((adj B s).homEquiv M N).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, h]

private theorem counit_pi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (N : Derived B X) :
    (jAdj B s).counit.app N ≫ (pi B s).app N = 𝟙 _ := by
  have := jAdj_unit_isIso B s
  apply clopen_map_injective B s
  rw [Functor.map_comp, pi_image]
  apply (cancel_epi ((jAdj B s).unit.app ((G B s).obj N))).1
  rw [← Category.assoc, (jAdj B s).right_triangle_components]
  erw [Category.id_comp, (G B s).map_id, Category.comp_id]

private theorem counit_precomp_injective {U X W : Scheme.{u}}
    (s : U ⟶ X) (b : X ⟶ W) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion b] (M : Derived B X) (Y : Derived B U)
    (f g : (J B b).obj M ⟶ (J B b).obj ((J B s).obj Y))
    (h : (J B b).map ((jAdj B s).counit.app M) ≫ f =
      (J B b).map ((jAdj B s).counit.app M) ≫ g) : f = g := by
  have := jAdj_unit_isIso B b
  let ff := (jAdj B b).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let f₀ := (J B b).preimage f
  let g₀ := (J B b).preimage g
  have h₀ : (jAdj B s).counit.app M ≫ f₀ = (jAdj B s).counit.app M ≫ g₀ := by
    apply (J B b).map_injective
    simpa only [f₀, g₀, Functor.map_comp, Functor.map_preimage] using h
  have := jAdj_unit_isIso B s
  have hε : IsIso ((G B s).map ((jAdj B s).counit.app M)) := by
    have hc : IsIso ((jAdj B s).unit.app ((G B s).obj M) ≫
        (G B s).map ((jAdj B s).counit.app M)) := by
      rw [(jAdj B s).right_triangle_components]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left ((jAdj B s).unit.app ((G B s).obj M)) _
  have h₁ : (G B s).map f₀ = (G B s).map g₀ := by
    apply (cancel_epi ((G B s).map ((jAdj B s).counit.app M))).1
    simpa only [Functor.map_comp] using congrArg (G B s).map h₀
  have h₂ := clopen_map_injective B s h₁
  have h₃ := congrArg (J B b).map h₂
  simpa only [f₀, g₀, Functor.map_preimage] using h₃

private theorem identity_open_unit (S : Scheme.{u}) (N : Derived B S) :
    (jAdj B (𝟙 S)).unit.app N ≫ (gId B S).hom.app ((J B (𝟙 S)).obj N) =
      (jId B S).inv.app N := by
  apply (cancel_mono ((jId B S).hom.app N)).1
  rw [Category.assoc, Iso.inv_hom_id_app]
  have hn := (gId B S).hom.naturality ((jId B S).hom.app N)
  dsimp only [Functor.id_map] at hn
  rw [← hn, ← Category.assoc, jId_transpose]
  exact Iso.inv_hom_id_app _ _

private theorem squareG_identity_bottom {U X S : Scheme.{u}}
    (s : U ⟶ X) (q : X ⟶ S) (N : Derived B S) :
    (squareG B (s ≫ q) s (𝟙 S) q (Category.comp_id _)).inv.app N =
      (G B (s ≫ q)).map ((gId B S).hom.app N) ≫ (gComp B s q).hom.app N := by
  have hu := congr_app (gComp_id_right B (s ≫ q)) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hu
  simp only [squareG, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, eqToIso.inv]
  apply (cancel_epi ((gComp B (s ≫ q) (𝟙 S)).hom.app N)).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [hu]
  rfl

private theorem jComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (N : Derived B U) :
    (jComp B (𝟙 U) j).hom.app N ≫
        (jCongr B (Category.id_comp j)).hom.app N =
      (J B j).map ((jId B U).hom.app N) := by
  let I := {f : U ⟶ X // IsOpenImmersion f}
  let L : I → Derived B U ⥤ Derived B X := fun f ↦ letI := f.2; J B f.1
  let R₀ : I → Derived B X ⥤ Derived B U := fun f ↦ G B f.1
  let a : ∀ f, L f ⊣ R₀ f := fun f ↦ letI := f.2; jAdj B f.1
  let f : I := ⟨(𝟙 U) ≫ j, inferInstance⟩
  let g : I := ⟨j, inferInstance⟩
  have e : f = g := Subtype.ext (Category.id_comp j)
  have hd : (gComp B (𝟙 U) j).symm ≪≫ eqToIso (congrArg R₀ e) =
      Functor.isoWhiskerLeft (G B j) (gId B U) ≪≫ Functor.rightUnitor (G B j) := by
    apply Iso.ext
    ext M
    have hh := congr_app (gComp_id_left B j) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hh
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    change (gComp B (𝟙 U) j).inv.app M ≫
      (eqToIso (congrArg (G B) (Category.id_comp j))).hom.app M =
        (gId B U).hom.app ((G B j).obj M) ≫ 𝟙 _
    rw [← hh, ← Category.assoc, Iso.inv_hom_id_app]
    erw [Category.id_comp, Category.comp_id]
  have hh := leftAdjointCompIso_transport L R₀ a (jAdj B (𝟙 U)) (jAdj B j)
    e (gComp B (𝟙 U) j).symm
  rw [hd, Adjunction.leftAdjointCompIso_id_comp _ _ _ _ rfl] at hh
  have hn := congrArg (fun t ↦ t.hom.app N) hh
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hn
  simpa only [jComp, jCongr, jId, Functor.comp_obj, Functor.id_obj,
    Category.comp_id] using hn

private theorem betaInv_open_comp_app {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g) (M : Derived B V) :
    (betaInv B b (k₁ ≫ j₁) (k ≫ j) g w).app M =
      (jComp B k₁ j₁).inv.app ((G B b).obj M) ≫
        (J B j₁).map ((betaInv B b k₁ k a wk).app M) ≫
        (betaInv B a j₁ j g wj).app ((J B k).obj M) ≫
        (G B g).map ((jComp B k j).hom.app M) := by
  have hp (N : Derived B X) :
      (G B b).map ((gComp B k j).hom.app N) ≫
        (squareG B b k₁ k a wk).inv.app ((G B j).obj N) ≫
        (G B k₁).map ((squareG B a j₁ j g wj).inv.app N) =
      (squareG B b (k₁ ≫ j₁) (k ≫ j) g w).inv.app N ≫
        (gComp B k₁ j₁).hom.app ((G B g).obj N) := by
    have hh := squareG_pasting_inv B g a b j k j₁ k₁
      wj.symm wk.symm w.symm N
    rw [squareG_flip B a j₁ j g wj, squareG_flip B b k₁ k a wk,
      squareG_flip B b (k₁ ≫ j₁) (k ≫ j) g w] at hh
    simp only [Iso.symm_inv] at hh
    apply (cancel_epi ((squareG B b (k₁ ≫ j₁) (k ≫ j) g w).hom.app N)).1
    rw [← Category.assoc, ← hh]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [(G B k₁).map_id, Category.comp_id]
  have hi := congr_app (betaInv_open_comp B k j k₁ j₁ a b g wk wj w hp) M
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk, TwoSquare.natTrans] at hi
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hi

private theorem betaInv_transport_opens {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j₁ j₂ : U ⟶ X) (k₁ k₂ : U' ⟶ X') (g : X' ⟶ X)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (ej : j₁ = j₂) (ek : k₁ = k₂)
    (w₁ : a ≫ j₁ = k₁ ≫ g) (w₂ : a ≫ j₂ = k₂ ≫ g) (N : Derived B U) :
    (jCongr B ek).inv.app ((G B a).obj N) ≫
        (betaInv B a k₁ j₁ g w₁).app N ≫
        (G B g).map ((jCongr B ej).hom.app N) =
      (betaInv B a k₂ j₂ g w₂).app N := by
  subst j₂
  subst k₂
  simp only [jCongr, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [(G B g).map_id, Category.id_comp, Category.comp_id]

private theorem betaInv_identity_bottom {U X S : Scheme.{u}}
    (s : U ⟶ X) (q : X ⟶ S) [IsOpenImmersion s] (N : Derived B S) :
    (betaInv B (s ≫ q) s (𝟙 S) q (Category.comp_id _)).app N =
      (J B s).map ((G B (s ≫ q)).map ((jId B S).inv.app N)) ≫
        (J B s).map ((gComp B s q).hom.app ((J B (𝟙 S)).obj N)) ≫
          (jAdj B s).counit.app ((G B q).obj ((J B (𝟙 S)).obj N)) := by
  change betaInvApp B _ _ _ _ _ N = _
  rw [betaInvApp, Adjunction.homEquiv_counit, squareG_identity_bottom,
    ← Category.assoc, ← Functor.map_comp, identity_open_unit]
  rw [Functor.map_comp, Category.assoc]

private theorem betaInv_identity_bottom_counit {U X S : Scheme.{u}}
    (s : U ⟶ X) (q : X ⟶ S) [IsOpenImmersion s] (N : Derived B S) :
    (betaInv B (s ≫ q) s (𝟙 S) q (Category.comp_id _)).app N ≫
        (G B q).map ((jId B S).hom.app N) =
      (J B s).map ((gComp B s q).hom.app N) ≫
        (jAdj B s).counit.app ((G B q).obj N) := by
  rw [betaInv_identity_bottom]
  have hn := (jAdj B s).counit.naturality ((G B q).map ((jId B S).hom.app N))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Category.assoc]
  rw [← hn]
  have hg := (gComp B s q).hom.naturality ((jId B S).hom.app N)
  dsimp only [Functor.comp_map] at hg
  rw [← (J B s).map_comp_assoc, ← (J B s).map_comp_assoc]
  simp only [Category.assoc]
  rw [← hg, ← (G B (s ≫ q)).map_comp_assoc, Iso.inv_hom_id_app]
  erw [(G B (s ≫ q)).map_id, Category.id_comp]
  simp only [Functor.id_obj]

private theorem betaInv_factor {V P W S T : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (q : P ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion i]
    (w₀ : q ≫ i = b ≫ p) (w : (s ≫ q) ≫ i = (s ≫ b) ≫ p)
    (N : Derived B S) :
    (betaInv B (s ≫ q) (s ≫ b) i p w).app N =
      (J B (s ≫ b)).map ((gComp B s q).hom.app N) ≫
        (jComp B s b).inv.app ((G B s).obj ((G B q).obj N)) ≫
        (J B b).map ((jAdj B s).counit.app ((G B q).obj N)) ≫
        (betaInv B q b i p w₀).app N := by
  let w' : (s ≫ q) ≫ ((𝟙 S) ≫ i) = (s ≫ b) ≫ p := by
    rw [Category.id_comp]; exact w
  have ht := betaInv_open_comp_app B (𝟙 S) i s b q (s ≫ q) p
    (Category.comp_id _) w₀ w' N
  have ht' := congrArg (fun f ↦ f ≫
    (G B p).map ((jCongr B (Category.id_comp i)).hom.app N)) ht
  simp only [Category.assoc] at ht'
  rw [← (G B p).map_comp, jComp_id_left] at ht'
  have hn := (betaInv B q b i p w₀).naturality ((jId B S).hom.app N)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← (J B b).map_comp_assoc, betaInv_identity_bottom_counit] at ht'
  rw [(J B b).map_comp] at ht'
  have hj := (jComp B s b).inv.naturality ((gComp B s q).hom.app N)
  dsimp only [Functor.comp_map] at hj
  simp only [Category.assoc] at ht'
  rw [← reassoc_of% hj] at ht'
  have hb := betaInv_transport_opens B (s ≫ q) ((𝟙 S) ≫ i) i
    (s ≫ b) (s ≫ b) p (Category.id_comp i) rfl w' w N
  simp only [jCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app] at hb
  erw [Category.id_comp] at hb
  simp only [jCongr] at ht'
  rw [hb] at ht'
  simpa only [Category.assoc, Functor.comp_obj, Functor.id_obj] using ht'

private theorem betaInv_factor_transport {V P W S T : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (q : P ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (r : V ⟶ S) (k : V ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion i] [IsOpenImmersion k]
    (er : s ≫ q = r) (ek : s ≫ b = k)
    (w₀ : q ≫ i = b ≫ p) (w : r ≫ i = k ≫ p) (N : Derived B S) :
    (betaInv B r k i p w).app N =
      (J B k).map ((gCongr B er).inv.app N ≫
        (gComp B s q).hom.app N) ≫
        (jCongr B ek).inv.app ((G B s).obj ((G B q).obj N)) ≫
        (jComp B s b).inv.app ((G B s).obj ((G B q).obj N)) ≫
        (J B b).map ((jAdj B s).counit.app ((G B q).obj N)) ≫
        (betaInv B q b i p w₀).app N := by
  subst r
  subst k
  simp only [gCongr_refl, jCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp]
  erw [Category.id_comp]
  exact betaInv_factor B s b q p i w₀ w N

private theorem betaInv_comp {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    [IsOpenImmersion j] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g))
    (M : Derived B U) :
    (J B j₂).map ((gComp B b a).hom.app M) ≫
      (betaInv B b j₂ j₁ h w₂).app ((G B a).obj M) ≫ (G B h).map ((betaInv B a j₁ j g w₁).app M) =
        (betaInv B (b ≫ a) j₂ j (h ≫ g) w).app M ≫ (gComp B h g).hom.app ((J B j).obj M) := by
  exact transposed_pasting (jAdj B j) (jAdj B j₁) (jAdj B j₂)
    (gComp B b a).hom (gComp B h g).hom
    (squareG B a j₁ j g w₁).inv (squareG B b j₂ j₁ h w₂).inv
    (squareG B (b ≫ a) j₂ j (h ≫ g) w).inv
    (betaInv B a j₁ j g w₁) (betaInv B b j₂ j₁ h w₂)
    (betaInv B (b ≫ a) j₂ j (h ≫ g) w)
    (betaInv_unit B a j₁ j g w₁) (betaInv_unit B b j₂ j₁ h w₂)
    (betaInv_unit B (b ≫ a) j₂ j (h ≫ g) w)
    (squareG_pasting_inv B j j₁ j₂ g h a b w₁ w₂ w) M

private theorem betaInv_transport_vertical {V S W T : Scheme.{u}}
    (r₀ r₁ : V ⟶ S) (k : V ⟶ W) (i : S ⟶ T) (p₀ p₁ : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (er : r₀ = r₁) (ep : p₀ = p₁)
    (h₀ : r₀ ≫ i = k ≫ p₀) (h₁ : r₁ ≫ i = k ≫ p₁) (N : Derived B S) :
    (J B k).map ((eqToIso (congrArg (G B) er)).inv.app N) ≫
        (betaInv B r₀ k i p₀ h₀).app N ≫
        (eqToIso (congrArg (G B) ep)).hom.app ((J B i).obj N) =
      (betaInv B r₁ k i p₁ h₁).app N := by
  subst r₁
  subst p₁
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
  erw [(J B k).map_id, Category.id_comp, Category.comp_id]

private theorem squareG_hom_comp {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (h : k ≫ p = r ≫ i) (N : Derived B T) :
    (squareG B k r p i h).hom.app N =
      (gComp B r i).inv.app N ≫
        (eqToIso (congrArg (G B) h)).inv.app N ≫ (gComp B k p).hom.app N := by
  have hs : (squareG B k r p i h).hom =
      (gComp B r i).inv ≫ (eqToIso (congrArg (G B) h)).inv ≫ (gComp B k p).hom := by
    simp only [squareG, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
  exact congr_app hs N

private theorem betaInv_cube {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c) (N : Derived B S) :
    (betaInv B r₁ k₁ i₁ p₁ h₁.symm).app ((G B c).obj N) ≫
        (G B p₁).map ((betaInv B c i₁ i b wi).app N) ≫
        (squareG B a p₁ p b wp).hom.app ((J B i).obj N) =
      (J B k₁).map ((squareG B d r₁ r c wr).hom.app N) ≫
        (betaInv B d k₁ k a wk).app ((G B r).obj N) ≫
        (G B a).map ((betaInv B r k i p h.symm).app N) := by
  let w₀ : (d ≫ r) ≫ i = k₁ ≫ (a ≫ p) := by
    calc
      (d ≫ r) ≫ i = d ≫ (r ≫ i) := Category.assoc _ _ _
      _ = d ≫ (k ≫ p) := by rw [← h]
      _ = (d ≫ k) ≫ p := (Category.assoc _ _ _).symm
      _ = (k₁ ≫ a) ≫ p := by rw [wk]
      _ = k₁ ≫ (a ≫ p) := Category.assoc _ _ _
  let w₁ : (r₁ ≫ c) ≫ i = k₁ ≫ (p₁ ≫ b) := by
    rw [← wr, ← wp]
    exact w₀
  have hv := betaInv_comp B i k k₁ p a r d h.symm wk w₀ N
  have hv₁ := betaInv_comp B i i₁ k₁ b p₁ c r₁ wi h₁.symm w₁ N
  have ht := betaInv_transport_vertical B (d ≫ r) (r₁ ≫ c) k₁ i
    (a ≫ p) (p₁ ≫ b) wr wp w₀ w₁ N
  have ht' : (betaInv B (r₁ ≫ c) k₁ i (p₁ ≫ b) w₁).app N ≫
      (eqToIso (congrArg (G B) wp)).inv.app ((J B i).obj N) =
      (J B k₁).map ((eqToIso (congrArg (G B) wr)).inv.app N) ≫
        (betaInv B (d ≫ r) k₁ i (a ≫ p) w₀).app N := by
    rw [← ht]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hv₁' : (betaInv B r₁ k₁ i₁ p₁ h₁.symm).app ((G B c).obj N) ≫
      (G B p₁).map ((betaInv B c i₁ i b wi).app N) =
      (J B k₁).map ((gComp B r₁ c).inv.app N) ≫
        (betaInv B (r₁ ≫ c) k₁ i (p₁ ≫ b) w₁).app N ≫
        (gComp B p₁ b).hom.app ((J B i).obj N) := by
    apply (cancel_epi ((J B k₁).map ((gComp B r₁ c).hom.app N))).1
    rw [← (J B k₁).map_comp_assoc, Iso.hom_inv_id_app]
    erw [(J B k₁).map_id, Category.id_comp]
    exact hv₁
  rw [squareG_hom_comp, squareG_hom_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hv₁']
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% ht', ← hv]

private theorem beta_inv_eq {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (k : U' ⟶ X') (i : U ⟶ X) (p : X' ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion k] (w : a ≫ i = k ≫ p)
    (sq : IsPullback a k i p) :
    (beta B a k i p w sq).inv = betaInv B a k i p w := by
  rfl

attribute [local irreducible] beta

private theorem betaInv_alpha {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (N : Derived B S) :
    (betaInv B r k i p h.symm).app N ≫ (alpha B k r p i h).app N = 𝟙 _ := by
  let s := squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  let : IsOpenImmersion s := squareLift_open k r p i h
  let : IsClosedImmersion s := squareLift_closed k r p i h
  let ek : s ≫ b = k := pullback.lift_fst k r h
  let er : s ≫ q = r := pullback.lift_snd k r h
  let w₀ : q ≫ i = b ≫ p := pullback.condition.symm
  have hf := betaInv_factor_transport B s b q p i r k er ek w₀ h.symm N
  exact projectedComparison_cancel_of_factor
    (J B i) (G B p) (G B q) (G B s) (J B s) (J B b)
    (J B (s ≫ b)) (J B k) (G B (s ≫ q)) (G B r)
    (beta B q b i p w₀ (IsPullback.of_hasPullback p i).flip)
    (jAdj B s).counit (pi B s) (jComp B s b) (jCongr B ek)
    (gComp B s q).symm (gCongr B er) (counit_pi B s)
    (alpha B k r p i h) (alpha_def B k r p i h)
    (betaInv B q b i p w₀)
    (beta_inv_eq B q b i p w₀ (IsPullback.of_hasPullback p i).flip).symm N
    ((betaInv B r k i p h.symm).app N) hf

private theorem betaInv_precomp_injective {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (N : Derived B S) (Y : Derived B V)
    (f g : (G B p).obj ((J B i).obj N) ⟶ (J B k).obj Y)
    (hfg : (betaInv B r k i p h.symm).app N ≫ f =
      (betaInv B r k i p h.symm).app N ≫ g) : f = g := by
  let s := pullback.lift k r h
  let b := pullback.fst p i
  let q := pullback.snd p i
  let : IsOpenImmersion s := squareLift_open k r p i h
  let : IsClosedImmersion s := squareLift_closed k r p i h
  let ek : s ≫ b = k := pullback.lift_fst k r h
  let er : s ≫ q = r := pullback.lift_snd k r h
  let w₀ : q ≫ i = b ≫ p := pullback.condition.symm
  have hf := betaInv_factor_transport B s b q p i r k er ek w₀ h.symm N
  rw [hf] at hfg
  simp only [Category.assoc] at hfg
  have h₁ := (cancel_epi ((J B k).map
    ((gCongr B er).inv.app N ≫ (gComp B s q).hom.app N))).1 hfg
  have h₂ := (cancel_epi ((jCongr B ek).inv.app
    ((G B s).obj ((G B q).obj N)))).1 h₁
  have h₃ := (cancel_epi ((jComp B s b).inv.app
    ((G B s).obj ((G B q).obj N)))).1 h₂
  let e := jComp B s b ≪≫ jCongr B ek
  have h₄ := congrArg (fun v ↦ v ≫ e.inv.app Y) h₃
  simp only [Category.assoc] at h₄
  have hx := counit_precomp_injective B s b ((G B q).obj N) Y
    ((betaInv B q b i p w₀).app N ≫ f ≫ e.inv.app Y)
    ((betaInv B q b i p w₀).app N ≫ g ≫ e.inv.app Y) h₄
  have := betaInv_isIso B q b i p w₀ (IsPullback.of_hasPullback p i).flip
  apply (cancel_mono (e.inv.app Y)).1
  apply (cancel_epi ((betaInv B q b i p w₀).app N)).1
  simpa only [Category.assoc] using hx

/-- Cartesian squares recover beta from the intrinsic clopen construction.
Source: Stacks, Tag 0F7B and blueprint, fourth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: factor the reverse open-unit comparison through the clopen lift. The
clopen counit followed by pi is identity, so betaInv followed by alpha is identity.
For a cartesian square betaInv is invertible, and cancelling it identifies alpha with beta. -/
theorem alpha_cartesian {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    alpha B k r p i h = (beta B r k i p h.symm hsq.flip).hom := by
  ext N
  have := betaInv_isIso B r k i p h.symm hsq.flip
  apply (cancel_epi ((betaInv B r k i p h.symm).app N)).1
  rw [betaInv_alpha B k r p i h N]
  rw [← beta_inv_eq B r k i p h.symm hsq.flip]
  exact (beta B r k i p h.symm hsq.flip).inv_hom_id_app N |>.symm


private theorem alpha_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived B U),
      (alpha B j (𝟙 U) (𝟙 X) j h).app M ≫
          (J B j).map ((gId B U).hom.app M) =
        (gId B X).hom.app ((J B j).obj M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived B X),
      (alpha B (𝟙 U) p p (𝟙 X) h).app M ≫
          (jId B U).hom.app ((G B p).obj M) =
        (G B p).map ((jId B X).hom.app M)) := by
  constructor
  · intro U X j _ _ h M
    rw [alpha_cartesian B j (𝟙 U) (𝟙 X) j h (IsPullback.of_id_snd (f := j))]
    exact beta_id B j h.symm (IsPullback.of_id_snd (f := j)).flip M
  · intro U X p _ h M
    rw [alpha_cartesian B (𝟙 U) p p (𝟙 X) h (IsPullback.of_id_fst (f := p))]
    exact beta_id_open B p h.symm (IsPullback.of_id_fst (f := p)).flip M



/-- Intrinsic alpha agrees with vertical pasting on every input.
Source: Stacks, Tag 0F7C and blueprint, fifth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: precomposition by the reverse comparison detects maps into the upper
open extension. The reverse vertical pasting equation reduces both sides to the
same pullback compositor after cancelling betaInv followed by alpha in each square. -/
theorem alpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Derived B E) :
    (gComp B p₁ p₂).hom.app ((J B j).obj N) ≫
        (G B p₁).map ((alpha B i r₂ p₂ j h₂).app N) ≫
        (alpha B k r₁ p₁ i h₁).app ((G B r₂).obj N) =
      (alpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (J B k).map ((gComp B r₁ r₂).hom.app N) := by
  apply betaInv_precomp_injective B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h N
    ((G B r₁).obj ((G B r₂).obj N))
  rw [← reassoc_of% (betaInv_comp B j i k p₂ p₁ r₂ r₁ h₂.symm h₁.symm h.symm N)]
  rw [← (G B p₁).map_comp_assoc, betaInv_alpha B i r₂ p₂ j h₂ N]
  erw [(G B p₁).map_id, Category.id_comp]
  rw [betaInv_alpha B k r₁ p₁ i h₁ ((G B r₂).obj N)]
  rw [reassoc_of% (betaInv_alpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h N)]
  exact Category.comp_id _

/-- Intrinsic alpha agrees with horizontal pasting on every input.
Source: Stacks, Tag 0F7D and blueprint, fifth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: normalize by the lower open compositor and precompose by the total
reverse comparison. Its open-composition equation reduces the two sides to identity,
using the two betaInv-alpha cancellation equations and the upper open compositor. -/
theorem alpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Derived B C) :
    (G B q).map ((jComp B i j).hom.app N) ≫
        (alpha B (k ≫ l) r q (i ≫ j) h).app N =
      (alpha B l p q j h₂).app ((J B i).obj N) ≫
        (J B l).map ((alpha B k r p i h₁).app N) ≫
        (jComp B k l).hom.app ((G B r).obj N) := by
  suffices hn : (alpha B (k ≫ l) r q (i ≫ j) h).app N =
      (G B q).map ((jComp B i j).inv.app N) ≫
        (alpha B l p q j h₂).app ((J B i).obj N) ≫
        (J B l).map ((alpha B k r p i h₁).app N) ≫
        (jComp B k l).hom.app ((G B r).obj N) by
    rw [hn, ← (G B q).map_comp_assoc, Iso.hom_inv_id_app]
    erw [(G B q).map_id, Category.id_comp]
  apply betaInv_precomp_injective B (k ≫ l) r q (i ≫ j) h N ((G B r).obj N)
  rw [betaInv_alpha B (k ≫ l) r q (i ≫ j) h N]
  rw [betaInv_open_comp_app B i j k l p r q h₁.symm h₂.symm h.symm N]
  simp only [Category.assoc]
  rw [← (G B q).map_comp_assoc, Iso.hom_inv_id_app]
  erw [(G B q).map_id, Category.id_comp]
  rw [reassoc_of% (betaInv_alpha B l p q j h₂ ((J B i).obj N))]
  rw [← (J B l).map_comp_assoc, betaInv_alpha B k r p i h₁ N]
  erw [(J B l).map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

-- The reverse cube needs only commutativity; retain the original pullback hypotheses.
set_option linter.unusedVariables false in
/-- Intrinsic alpha commutes with the canonical pullback cube.
Source: Stacks, Tag 0F7F and blueprint, fifth proof step
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: paste reverse comparisons along the two diagonals of the cube. Transport
along the two vertical-face equalities identifies these pastings. Precompose the
normalized alpha cube by the upper reverse comparison; its injectivity and the two
betaInv-alpha cancellation equations prove equality. The proof only needs the open
faces to be cartesian, retaining all hypotheses of the original statement. -/
theorem alpha_baseChange {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) (N : Derived B S) :
    (squareG B a p₁ p b wp).hom.app ((J B i).obj N) ≫
        (G B a).map ((alpha B k r p i h).app N) ≫
        (beta B d k₁ k a wk sk).hom.app ((G B r).obj N) ≫
        (J B k₁).map ((squareG B d r₁ r c wr).inv.app N) =
      (G B p₁).map ((beta B c i₁ i b wi si).hom.app N) ≫
        (alpha B k₁ r₁ p₁ i₁ h₁).app ((G B c).obj N) := by
  have hc := betaInv_cube B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr N
  rw [← beta_inv_eq B c i₁ i b wi si, ← beta_inv_eq B d k₁ k a wk sk] at hc
  have hx : (G B p₁).map ((beta B c i₁ i b wi si).inv.app N) ≫
      (squareG B a p₁ p b wp).hom.app ((J B i).obj N) ≫
      (G B a).map ((alpha B k r p i h).app N) ≫
      (beta B d k₁ k a wk sk).hom.app ((G B r).obj N) ≫
      (J B k₁).map ((squareG B d r₁ r c wr).inv.app N) =
      (alpha B k₁ r₁ p₁ i₁ h₁).app ((G B c).obj N) := by
    apply betaInv_precomp_injective B k₁ r₁ p₁ i₁ h₁
      ((G B c).obj N) ((G B r₁).obj ((G B c).obj N))
    rw [betaInv_alpha B k₁ r₁ p₁ i₁ h₁ ((G B c).obj N)]
    rw [reassoc_of% hc]
    rw [← (G B a).map_comp_assoc, betaInv_alpha B k r p i h N]
    erw [(G B a).map_id, Category.id_comp]
    simp only [Iso.inv_hom_id_app_assoc, ← (J B k₁).map_comp,
      Iso.hom_inv_id_app]
    exact (J B k₁).map_id _
  apply (cancel_epi ((G B p₁).map ((beta B c i₁ i b wi si).inv.app N))).1
  rw [hx, ← (G B p₁).map_comp_assoc, Iso.inv_hom_id_app]
  erw [(G B p₁).map_id, Category.id_comp]

end CartesianNormalization

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

/-- The finite comparison retains the specified witness of the normalization theorem. -/
theorem finiteGamma_eq_secondWitness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    finiteGamma Λ k r p i h =
      secondWitness (Etale.properOpenInterchangeCoherence Λ) k i r p h := by
  unfold finiteGamma
  rfl

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

private theorem comparison_transport
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) (a : F ⟶ G)
    {O M : C} (e : O ≅ M) {A Z P Q : D}
    (s : A ≅ F.obj O) (t : Z ≅ G.obj O)
    (es : P ≅ F.obj M) (et : Q ≅ G.obj M) (v : P ⟶ Q) (f : A ⟶ Z)
    (he : es.hom ≫ a.app M = v ≫ et.hom)
    (hf : s.hom ≫ a.app O = f ≫ t.hom) :
    (s ≪≫ F.mapIso e ≪≫ es.symm).hom ≫ v =
      f ≫ (t ≪≫ G.mapIso e ≪≫ et.symm).hom := by
  apply (cancel_mono et.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← he, Iso.inv_hom_id_assoc, a.naturality]
  rw [← Category.assoc, hf]
  simp only [Category.assoc]

/-- The n-th evaluation is this particular normalized finite comparison, including
refinements, and not just some isomorphism between the same objects.
Source: Stacks, Tag 0F7B and blueprint, seventh and eighth proof steps
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: evaluation preserves the exact functors, and its R comparison is the mate
preserving their units and counits. Scalar restriction preserves the identity/zero
clopen projector. The site comparison carries the two clopen components to the
same components. Transpose under the proper adjunction: the direct-image unit
normalization cancels its counit, leaving the same compared clopen alpha on both
sides. The finite etale node has precisely this transpose, by its section and
K-injective unit normalization. Injectivity of the adjunction Hom equivalence
proves the equation, including when r is identity and the lift is a clopen section. -/
theorem gamma_evaluation {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived B V) (n : ℕ)
    (w : ScalarEtaleOrigin B V ((ev B V n).obj M)) :
    (finiteSource B r i M n w).hom ≫ (ev B T n).map ((gamma B k r p i h).app M) =
      (HD B T w.Λ w.φ).map ((finiteGamma w.Λ k r p i h).hom.app w.origin.L) ≫
        (finiteTarget B k p M n w).hom := by
  let F := (moduleDirectImage B r).rightDerivedFunctor ⋙ (moduleJ B i).mapDerivedCategory
  let G₀ := (moduleJ B k).mapDerivedCategory ⋙ (moduleDirectImage B p).rightDerivedFunctor
  let es := (evalJ B i n).app ((R B r).obj M) ≪≫
    (moduleJ B i).mapDerivedCategory.mapIso
      ((@asIso _ _ _ _ (evalR B r n) (evalR_isIso B r n)).app M)
  let et := (@asIso _ _ _ _ (evalR B p n) (evalR_isIso B p n)).app ((J B k).obj M) ≪≫
    (moduleDirectImage B p).rightDerivedFunctor.mapIso ((evalJ B k n).app M)
  have he : es.hom ≫ (singleGamma B k r p i h).app ((ev B V n).obj M) =
      (ev B T n).map ((gamma B k r p i h).app M) ≫ et.hom := by
    simpa only [es, et, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      asIso_hom, Category.assoc] using gamma_single_evaluation B k r p i h M n
  have hf : (singleFiniteSource B r i w.Λ w.φ w.origin.L).hom ≫
      (singleGamma B k r p i h).app ((HD B V w.Λ w.φ).obj w.origin.L) =
      (HD B T w.Λ w.φ).map ((finiteGamma w.Λ k r p i h).hom.app w.origin.L) ≫
        (singleFiniteTarget B k p w.Λ w.φ w.origin.L).hom := by
    simpa only [finiteGamma, secondWitness] using
      singleGamma_finite_normalization B k r p i h w.Λ w.φ w.origin.L
  have ht := comparison_transport F G₀ (singleGamma B k r p i h) (originIso B w)
    (singleFiniteSource B r i w.Λ w.φ w.origin.L)
    (singleFiniteTarget B k p w.Λ w.φ w.origin.L) es et
    ((ev B T n).map ((gamma B k r p i h).app M))
    ((HD B T w.Λ w.φ).map ((finiteGamma w.Λ k r p i h).hom.app w.origin.L)) he hf
  simpa only [finiteSource, finiteTarget, singleFiniteSource, singleFiniteTarget,
    es, et, F, G₀, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    asIso_hom, asIso_inv, Functor.comp_map,
    Functor.map_comp, Category.assoc] using ht


/-- Proper/open interchange is invertible for independently bounded finite etale
origins at every positive level, with no uniform bound on those origins.
Source: Stacks, Tag 0F7B and blueprint, steps 7--9
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: evaluation of a K-injective strict tower is K-injective, so evaluation
commutes with R and its adjunction units and counits. Scalar restriction commutes
with G, J and R by the normalized change-of-ring adjunction, not by any claim that
it preserves K-injectives. The identity/zero clopen projector is unchanged by
scalar restriction. At an etale origin the canonical direct-image comparisons for
proper (hence qcqs) maps and open comparisons identify this mate with the normalized
finite etale comparison of properOpenInterchangeCoherence. It is an isomorphism.
Thus every evaluated map is invertible. Tower cohomology is levelwise, so the map
induces an isomorphism in every degree, and the unbounded-derived cohomology
criterion proves invertibility. This detects isomorphisms, not equality of maps. -/
theorem gamma_isIso {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived B V)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B V ((ev B V n).obj M))) :
    IsIso ((gamma B k r p i h).app M) := by
  have heval (n : ℕ) : IsIso ((ev B T n).map ((gamma B k r p i h).app M)) := by
    let w := Classical.choice (hM n)
    have heq := gamma_evaluation B k r p i h M n w
    have : IsIso ((finiteSource B r i M n w).hom ≫
        (ev B T n).map ((gamma B k r p i h).app M)) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_left (finiteSource B r i M n w).hom _
  apply (DerivedCategory.isIso_iff _ _).2
  intro q
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  have := heval n.unop
  exact (NatIso.isIso_map_iff
    (((evaluation ℕᵒᵖ (Modules B T)).obj n).mapDerivedCategoryHomologyFunctorIso q)
    ((gamma B k r p i h).app M)).2 (by
      change IsIso ((DerivedCategory.homologyFunctor (Modules B T) q).map
        ((ev B T n.unop).map ((gamma B k r p i h).app M)))
      infer_instance)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Vertical, horizontal and base-change coherence for every commutative proper/open
square, as equalities in derived strict-tower categories, without assuming evaluation
faithful. Source: Stacks, Tags 0F7C, 0F7D and 0F7F, and blueprint, steps 5, 6, 10, 11
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: for alpha, pull the clopen decompositions to each test object. In a vertical
or horizontal pasting the selected opens are nested, so successive component
projections equal the outer component projection. Base change pulls both clopen
components and the identity/zero projector to the corresponding components. Verify
these equations on their intersections using sheaf uniqueness. Apply the exact
functors termwise to towers and complexes, then use localization uniqueness to
descend the equations. Take proper-adjunction mates with composition adjunctions.
Mate pasting gives the two composition laws; the pullback cube gives the base-change
law. Associativity of normalized compositors makes all parenthesizations agree. -/
theorem normalizedProperOpenCalculus :
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived B A),
      (J B j).map ((rComp B r₁ r₂).hom.app M) ≫
          (gamma B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (rComp B p₁ p₂).inv.app ((J B k).obj M) =
        (gamma B i r₂ p₂ j h₂).app ((R B r₁).obj M) ≫
          (R B p₂).map ((gamma B k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived B A),
      (jComp B i j).hom.app ((R B r).obj M) ≫
          (gamma B (k ≫ l) r q (i ≫ j) h).app M ≫
          (R B q).map ((jComp B k l).inv.app M) =
        (J B j).map ((gamma B k r p i h₁).app M) ≫
          (gamma B l p q j h₂).app ((J B k).obj M)) ∧
    (∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
      (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) (M : Derived B V),
      (G B b).map ((gamma B k r p i h).app M) ≫
          (exchange B a p₁ p b wp).app ((J B k).obj M) ≫
          (R B p₁).map ((beta B d k₁ k a wk sk).hom.app M) =
        (beta B c i₁ i b wi si).hom.app ((R B r).obj M) ≫
          (J B i₁).map ((exchange B d r₁ r c wr).app M) ≫
          (gamma B k₁ r₁ p₁ i₁ h₁).app ((G B d).obj M)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A C E B₀ D F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    have hs : alpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h =
        (((TwoSquare.mk _ _ _ _ (alpha B i r₂ p₂ j h₂)).vComp
          (TwoSquare.mk _ _ _ _ (alpha B k r₁ p₁ i h₁))).whiskerRight
            (gComp B p₁ p₂).hom).whiskerLeft (gComp B r₁ r₂).inv := by
      ext N
      simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
        TwoSquare.vComp_app]
      apply (cancel_mono ((J B k).map ((gComp B r₁ r₂).hom.app N))).1
      simpa [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
        Iso.hom_inv_id_app, Functor.map_id, Category.comp_id,
        TwoSquare.mk, TwoSquare.natTrans] using
        (alpha_vertical B k i j r₁ r₂ p₁ p₂ h₁ h₂ h N).symm
    have hm := congrArg (fun α ↦ (mateEquiv (adj B (r₁ ≫ r₂))
      (adj B (p₁ ≫ p₂)) α).app M) hs
    rw [conjugateEquiv_mateEquiv_vcomp _ ((adj B r₂).comp (adj B r₁)),
      mateEquiv_conjugateEquiv_vcomp _ ((adj B p₂).comp (adj B p₁)),
      mateEquiv_hcomp] at hm
    simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.hComp_app] at hm
    change (gamma B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M =
      (J B j).map ((rComp B r₁ r₂).inv.app M) ≫
        ((gamma B i r₂ p₂ j h₂).app ((R B r₁).obj M) ≫
          (R B p₂).map ((gamma B k r₁ p₁ i h₁).app M)) ≫
            (rComp B p₁ p₂).hom.app ((J B k).obj M) at hm
    rw [hm]
    simp [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Category.id_comp]
  · intro A C E B₀ D F k l i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    have hs : alpha B (k ≫ l) r q (i ≫ j) h =
        (((TwoSquare.mk _ _ _ _ (alpha B k r p i h₁)).hComp
          (TwoSquare.mk _ _ _ _ (alpha B l p q j h₂))).whiskerTop
            (jComp B i j).inv).whiskerBottom (jComp B k l).hom := by
      ext N
      simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
        TwoSquare.hComp_app]
      apply (cancel_epi ((G B q).map ((jComp B i j).hom.app N))).1
      simpa [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
        Functor.map_id, Category.id_comp, TwoSquare.mk, TwoSquare.natTrans] using
        alpha_horizontal B k l i j r p q h₁ h₂ h N
    have hm := congrArg (fun α ↦ (mateEquiv (adj B r) (adj B q) α).app M) hs
    rw [mateEquiv_whiskerTop_whiskerBottom,
      mateEquiv_vcomp (adj B r) (adj B p) (adj B q)] at hm
    simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
      TwoSquare.vComp_app] at hm
    simp only [Category.assoc] at hm
    change (gamma B (k ≫ l) r q (i ≫ j) h).app M =
      (jComp B i j).inv.app ((R B r).obj M) ≫
        (J B j).map ((gamma B k r p i h₁).app M) ≫
        (gamma B l p q j h₂).app ((J B k).obj M) ≫
        (R B q).map ((jComp B k l).hom.app M) at hm
    rw [hm]
    simp [Category.assoc, ← Functor.map_comp]
  · intro V W S T V₁ W₁ S₁ T₁ k i r p k₁ i₁ r₁ p₁ a b c d
      _ _ _ _ _ _ _ _ _ _ _ _ h h₁ wk wi wp wr sk si sp sr M
    let α := TwoSquare.mk _ _ _ _ (alpha B k r p i h)
    let α₁ := TwoSquare.mk _ _ _ _ (alpha B k₁ r₁ p₁ i₁ h₁)
    let δp := TwoSquare.mk _ _ _ _ (squareG B a p₁ p b wp).hom
    let δr := TwoSquare.mk _ _ _ _ (squareG B d r₁ r c wr).hom
    have hs : (α.hComp δp).whiskerBottom (beta B d k₁ k a wk sk).hom =
        (δr.hComp α₁).whiskerTop (beta B c i₁ i b wi si).hom := by
      ext N
      simp only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app,
        TwoSquare.hComp_app, α, α₁, δp, δr, TwoSquare.mk, TwoSquare.natTrans]
      apply (cancel_mono
        ((J B k₁).map ((squareG B d r₁ r c wr).inv.app N))).1
      simpa [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
        Functor.map_id, Category.comp_id] using
        alpha_baseChange B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si sp sr N
    have hm := congrArg (fun σ ↦ (mateEquiv (adj B r) (adj B p₁) σ).app M) hs
    rw [mateEquiv_whiskerBottom, mateEquiv_vcomp (adj B r) (adj B p) (adj B p₁)] at hm
    have ht : mateEquiv (adj B r) (adj B p₁)
        ((δr.hComp α₁).whiskerTop (beta B c i₁ i b wi si).hom) =
        (mateEquiv (adj B r) (adj B p₁) (δr.hComp α₁)).whiskerRight
          (beta B c i₁ i b wi si).hom := by
      ext N
      simp [mateEquiv, TwoSquare.whiskerTop, TwoSquare.whiskerRight]
    rw [ht, mateEquiv_vcomp (adj B r) (adj B r₁) (adj B p₁)] at hm
    simpa [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
      TwoSquare.vComp_app, α, α₁, δp, δr, gamma, exchange,
      TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using hm

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

/-- Identity normalizations of gamma in both directions.
Source: Stacks, Tags 0F7B and 07A7, blueprint, steps 6 and 10
(blueprint: lem-cbc-strict-tower-proper-open-calculus).
Proof: the clopen projection is identity for either identity square. Its alpha is the
canonical inverse-image/open-extension identity; taking the mate and using the
triangle identities gives the corresponding identity on direct image or extension. -/
theorem gamma_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived B U),
      (gamma B j (𝟙 U) (𝟙 X) j h).app M ≫
          (rId B X).hom.app ((J B j).obj M) =
        (J B j).map ((rId B U).hom.app M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived B U),
      (gamma B (𝟙 U) p p (𝟙 X) h).app M ≫
          (R B p).map ((jId B U).hom.app M) =
        (jId B X).hom.app ((R B p).obj M)) := by
  constructor
  · intro U X j _ _ h M
    dsimp only [gamma, rId]
    exact mate_identity_vertical (adj B (𝟙 U)) (adj B (𝟙 X))
      (gId B U) (gId B X) (J B j) (alpha B j (𝟙 U) (𝟙 X) j h)
      (fun N ↦ (alpha_identities B).1 j h N) M
  · intro U X p _ h M
    dsimp only [gamma]
    exact mate_identity_horizontal (adj B p) (J B (𝟙 X)) (J B (𝟙 U))
      (jId B X) (jId B U) (alpha B (𝟙 U) p p (𝟙 X) h)
      (fun N ↦ (alpha_identities B).2 p h N) M

end GammaIdentities

end AlgebraicGeometry.ProEtale.StrictTower
