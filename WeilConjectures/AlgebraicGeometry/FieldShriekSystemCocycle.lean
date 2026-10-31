/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemCoherence
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemCoefficientLaws
import WeilConjectures.AlgebraicGeometry.FieldShriekSystemPullbackCocycle
import WeilConjectures.AlgebraicGeometry.IntegralResidueMatePasting

/-! # Whole-system proper/open coefficient cocycles

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
proof steps 5--7 of lem-sp-field-shriek-system-comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

open CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

attribute [local irreducible] coefficientMap HasDerivedCategory.standard scalarAssoc scalarUnit
set_option backward.defeqAttrib.useBackward true


private theorem mate_whisker
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F F' : A ⥤ C} {G G' : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (t : TwoSquare F L₁ L₂ G)
    (f : F' ⟶ F) (g : G ⟶ G') :
    (mateEquiv a₁ a₂ ((t.whiskerTop f).whiskerBottom g)).natTrans =
      Functor.whiskerLeft R₁ f ≫ (mateEquiv a₁ a₂ t).natTrans ≫ Functor.whiskerRight g R₂ := by
  ext N
  dsimp only [TwoSquare.natTrans]
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← a₂.unit_naturality_assoc]
  dsimp only [TwoSquare.natTrans]
  simp only [Functor.comp_map]
  have hg := congrArg R₂.map (g.naturality (a₁.counit.app N))
  simp only [R₂.map_comp] at hg
  rw [← reassoc_of% hg]
  simp


private theorem mate_composition
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    {S₁₂ : A ⥤ C} {S₂₃ : C ⥤ E} {S₁₃ : A ⥤ E}
    {T₁₂ : B ⥤ D} {T₂₃ : D ⥤ F} {T₁₃ : B ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (t₁₂ : TwoSquare S₁₂ L₁ L₂ T₁₂) (t₂₃ : TwoSquare S₂₃ L₂ L₃ T₂₃)
    (t₁₃ : TwoSquare S₁₃ L₁ L₃ T₁₃)
    (α : S₁₂ ⋙ S₂₃ ⟶ S₁₃) (β : T₁₂ ⋙ T₂₃ ⟶ T₁₃)
    (hc : ∀ M, t₂₃.app (S₁₂.obj M) ≫ T₂₃.map (t₁₂.app M) ≫
      β.app (L₁.obj M) = L₃.map (α.app M) ≫ t₁₃.app M) :
    ∀ N, S₂₃.map ((mateEquiv a₁ a₂ t₁₂).app N) ≫
      (mateEquiv a₂ a₃ t₂₃).app (T₁₂.obj N) ≫ R₃.map (β.app N) =
      α.app (R₁.obj N) ≫ (mateEquiv a₁ a₃ t₁₃).app N := by
  have ht : (TwoSquare.hComp t₁₂ t₂₃).whiskerBottom β = t₁₃.whiskerTop α := by
    ext M
    simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp] using hc M
  have hm := congrArg (fun t ↦ (mateEquiv a₁ a₃ t).natTrans) ht
  have hleft := mate_whisker a₁ a₃ (TwoSquare.hComp t₁₂ t₂₃) (𝟙 _) β
  have hright := mate_whisker a₁ a₃ t₁₃ α (𝟙 _)
  have hidtop : (TwoSquare.hComp t₁₂ t₂₃).whiskerTop (𝟙 _) =
      TwoSquare.hComp t₁₂ t₂₃ := by
    ext M
    simp [TwoSquare.whiskerTop]
  have hidbottom : (t₁₃.whiskerTop α).whiskerBottom (𝟙 _) = t₁₃.whiskerTop α := by
    ext M
    simp [TwoSquare.whiskerBottom]
  rw [hidtop] at hleft
  rw [hidbottom] at hright
  simp only [Functor.whiskerLeft_id', Category.id_comp] at hleft
  simp only [Functor.whiskerRight_id', Category.comp_id] at hright
  rw [hleft, hright] at hm
  have hh := mateEquiv_vcomp a₁ a₂ a₃ t₁₂ t₂₃
  rw [hh] at hm
  intro N
  simpa [TwoSquare.vComp] using congr_app hm N

private theorem mate_identity
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {S : A ⥤ A} {T : B ⥤ B}
    (t : TwoSquare S L L T) (α : S ⟶ 𝟭 _) (β : T ⟶ 𝟭 _)
    (hc : ∀ M, t.app M ≫ β.app (L.obj M) = L.map (α.app M)) :
    ∀ N, (mateEquiv a a t).app N ≫ R.map (β.app N) = α.app (R.obj N) := by
  have ht : t.whiskerBottom β = (TwoSquare.hId L).whiskerTop α := by
    ext M
    simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hId] using hc M
  have hm := congrArg (fun t ↦ (mateEquiv a a t).natTrans) ht
  have hleft := mate_whisker a a t (𝟙 _) β
  have hright := mate_whisker a a (TwoSquare.hId L) α (𝟙 _)
  have hidtop : t.whiskerTop (𝟙 _) = t := by
    ext M
    simp [TwoSquare.whiskerTop]
  have hidbottom : ((TwoSquare.hId L).whiskerTop α).whiskerBottom (𝟙 _) =
      (TwoSquare.hId L).whiskerTop α := by
    ext M
    simp [TwoSquare.whiskerBottom]
  rw [hidtop] at hleft
  rw [hidbottom] at hright
  simp only [Functor.whiskerLeft_id', Category.id_comp] at hleft
  simp only [Functor.whiskerRight_id', Category.comp_id] at hright
  rw [hleft, hright] at hm
  intro N
  have hn := congr_app hm N
  simpa [mateEquiv, TwoSquare.hId] using hn

private theorem inverse_path
    {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₄)
    (d : X₀ ≅ X₃) (e : X₃ ≅ X₄)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom) :
    c.inv ≫ b.inv ≫ a.inv = e.inv ≫ d.inv := by
  have hi : a ≪≫ b ≪≫ c = d ≪≫ e := Iso.ext h
  have := congrArg Iso.inv hi
  simpa using this

private theorem inverseMate_unit
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {S : A ⥤ A} {T : B ⥤ B} (q : TwoSquare R T S R)
    (c : 𝟭 _ ⟶ S) (d : 𝟭 _ ⟶ T)
    (hq : ∀ N, c.app (R.obj N) ≫ q.app N = R.map (d.app N)) (K : A) :
    L.map (c.app K) ≫ ((mateEquiv a a).symm q).app K = d.app (L.obj K) := by
  let p := ((mateEquiv a a).symm q).natTrans
  have hh := unit_mateEquiv_symm a a q K
  change S.map (a.unit.app K) ≫ q.app (L.obj K) =
    a.unit.app (S.obj K) ≫ R.map (p.app K) at hh
  have hu : c.app K ≫ a.unit.app (S.obj K) =
      a.unit.app K ≫ R.map (L.map (c.app K)) := a.unit.naturality (c.app K)
  have hn : a.unit.app K ≫ c.app (R.obj (L.obj K)) =
      c.app K ≫ S.map (a.unit.app K) := c.naturality (a.unit.app K)
  apply (a.homEquiv _ _).injective
  change a.unit.app K ≫ R.map (L.map (c.app K) ≫ p.app K) =
    a.unit.app K ≫ R.map (d.app (L.obj K))
  rw [R.map_comp, ← Category.assoc, ← hu, Category.assoc, ← hh,
    ← Category.assoc, ← hn, Category.assoc, hq]


private theorem comparison_paste
    {A₁ A₂ A₃ B₁ B₂ B₃ C₁ C₂ C₃ : Type*}
    [Category A₁] [Category A₂] [Category A₃]
    [Category B₁] [Category B₂] [Category B₃]
    [Category C₁] [Category C₂] [Category C₃]
    (J₁ : A₁ ⥤ B₁) (J₂ : A₂ ⥤ B₂) (J₃ : A₃ ⥤ B₃)
    (G₁ : B₁ ⥤ C₁) (G₂ : B₂ ⥤ C₂) (G₃ : B₃ ⥤ C₃)
    (S₁₂ : A₁ ⥤ A₂) (S₂₃ : A₂ ⥤ A₃) (S₁₃ : A₁ ⥤ A₃)
    (T₁₂ : B₁ ⥤ B₂) (T₂₃ : B₂ ⥤ B₃) (T₁₃ : B₁ ⥤ B₃)
    (U₁₂ : C₁ ⥤ C₂) (U₂₃ : C₂ ⥤ C₃) (U₁₃ : C₁ ⥤ C₃)
    (α : S₁₂ ⋙ S₂₃ ⟶ S₁₃) (β : T₁₂ ⋙ T₂₃ ⟶ T₁₃)
    (γ : U₁₂ ⋙ U₂₃ ⟶ U₁₃)
    (o₁₂ : J₁ ⋙ T₁₂ ⟶ S₁₂ ⋙ J₂) (o₂₃ : J₂ ⋙ T₂₃ ⟶ S₂₃ ⋙ J₃)
    (o₁₃ : J₁ ⋙ T₁₃ ⟶ S₁₃ ⋙ J₃)
    (p₁₂ : G₁ ⋙ U₁₂ ⟶ T₁₂ ⋙ G₂) (p₂₃ : G₂ ⋙ U₂₃ ⟶ T₂₃ ⋙ G₃)
    (p₁₃ : G₁ ⋙ U₁₃ ⟶ T₁₃ ⋙ G₃)
    (ho : ∀ M, T₂₃.map (o₁₂.app M) ≫ o₂₃.app (S₁₂.obj M) ≫ J₃.map (α.app M) =
      β.app (J₁.obj M) ≫ o₁₃.app M)
    (hp : ∀ N, U₂₃.map (p₁₂.app N) ≫ p₂₃.app (T₁₂.obj N) ≫ G₃.map (β.app N) =
      γ.app (G₁.obj N) ≫ p₁₃.app N) (M : A₁) :
    U₂₃.map (p₁₂.app (J₁.obj M) ≫ G₂.map (o₁₂.app M)) ≫
      (p₂₃.app (J₂.obj (S₁₂.obj M)) ≫ G₃.map (o₂₃.app (S₁₂.obj M))) ≫
      G₃.map (J₃.map (α.app M)) =
    γ.app (G₁.obj (J₁.obj M)) ≫ p₁₃.app (J₁.obj M) ≫ G₃.map (o₁₃.app M) := by
  have hn := p₂₃.naturality (o₁₂.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← G₃.map_comp_assoc, ← G₃.map_comp, Category.assoc, ho]
  simp only [G₃.map_comp]
  rw [reassoc_of% hp]

private theorem proper_composition (P : PurityFiniteSetting.{u}) (D : Models P)
    (cc : CoefficientLaws P D) (E F L : Index P) (h : E ≤ F) (k : F ≤ L)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (N : SpTowerShriek.D P.coefficients.l E.val Z) :
    (D.scalars F L k Y).T.map ((proper P D h g).app N) ≫
      (proper P D k g).app ((D.scalars E F h Z).T.obj N) ≫
      (SpTowerShriek.push P.coefficients.l L.val (D.base L) ((D.operations L).geometry g)).map
        ((scalarAssoc P D h k Z (cc.composition E F L h k Z)).hom.app N) =
    (scalarAssoc P D h k Y (cc.composition E F L h k Y)).hom.app
      ((SpTowerShriek.push P.coefficients.l E.val (D.base E)
        ((D.operations E).geometry g)).obj N) ≫ (proper P D (h.trans k) g).app N := by
  have hc := (field_shriek_system_pullback_cocycle P D E F L h k g
    (cc.composition E F L h k Z) (cc.composition E F L h k Y)
    (cc.identity E Z) (cc.identity E Y)).1
  exact mate_composition
    (SpTowerShriek.adjunction P.coefficients.l E.val (D.base E) ((D.operations E).geometry g))
    (SpTowerShriek.adjunction P.coefficients.l F.val (D.base F) ((D.operations F).geometry g))
    (SpTowerShriek.adjunction P.coefficients.l L.val (D.base L) ((D.operations L).geometry g))
    (D.pull E F h g).derived.hom (D.pull F L k g).derived.hom
    (D.pull E L (h.trans k) g).derived.hom
    (scalarAssoc P D h k Y (cc.composition E F L h k Y)).hom
    (scalarAssoc P D h k Z (cc.composition E F L h k Z)).hom
    (fun M ↦ by simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.comp_obj] using congr_app hc M) N

private theorem proper_identity (P : PurityFiniteSetting.{u}) (D : Models P)
    (cc : CoefficientLaws P D) (E : Index P)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (N : SpTowerShriek.D P.coefficients.l E.val Z) :
    (proper P D (E := E) (F := E) le_rfl g).app N ≫
      (SpTowerShriek.push P.coefficients.l E.val (D.base E) ((D.operations E).geometry g)).map
        ((scalarUnit P D E Z (cc.identity E Z)).hom.app N) =
    (scalarUnit P D E Y (cc.identity E Y)).hom.app
      ((SpTowerShriek.push P.coefficients.l E.val (D.base E)
        ((D.operations E).geometry g)).obj N) := by
  have hc := (field_shriek_system_pullback_cocycle P D E E E le_rfl le_rfl g
    (cc.composition E E E le_rfl le_rfl Z) (cc.composition E E E le_rfl le_rfl Y)
    (cc.identity E Z) (cc.identity E Y)).2
  exact mate_identity
    (SpTowerShriek.adjunction P.coefficients.l E.val (D.base E) ((D.operations E).geometry g))
    (D.pull E E le_rfl g).derived.hom
    (scalarUnit P D E Y (cc.identity E Y)).hom
    (scalarUnit P D E Z (cc.identity E Z)).hom
    (fun M ↦ by simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.comp_obj] using congr_app hc M) N


set_option maxHeartbeats 800000 in
-- The explicit open mate calculation needs more reduction heartbeats.
private theorem open_composition (P : PurityFiniteSetting.{u}) (D : Models P)
    (cc : CoefficientLaws P D) (E F L : Index P) (h : E ≤ F) (k : F ≤ L)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : SpTowerShriek.D P.coefficients.l E.val X) :
    (D.scalars F L k Z).T.map ((D.openIso E F h j).hom.app M) ≫
      (D.openIso F L k j).hom.app ((D.scalars E F h X).T.obj M) ≫
      (SpTowerShriek.openD P.coefficients.l L.val (D.base L)
        ((D.operations L).openOp j)).map
        ((scalarAssoc P D h k X (cc.composition E F L h k X)).hom.app M) =
    (scalarAssoc P D h k Z (cc.composition E F L h k Z)).hom.app
      ((SpTowerShriek.openD P.coefficients.l E.val (D.base E)
        ((D.operations E).openOp j)).obj M) ≫ (D.openIso E L (h.trans k) j).hom.app M := by
  let ax := scalarAssoc P D h k X (cc.composition E F L h k X)
  let az := scalarAssoc P D h k Z (cc.composition E F L h k Z)
  let rE := SpTowerShriek.pull P.coefficients.l E.val (D.base E) ((D.operations E).geometry j)
  let rL := SpTowerShriek.pull P.coefficients.l L.val (D.base L) ((D.operations L).geometry j)
  have hc := (field_shriek_system_pullback_cocycle P D E F L h k j
    (cc.composition E F L h k X) (cc.composition E F L h k Z)
    (cc.identity E X) (cc.identity E Z)).1
  have hi (N : SpTowerShriek.D P.coefficients.l E.val Z) :
      ax.inv.app (rE.obj N) ≫
        (D.scalars F L k X).T.map ((D.pull E F h j).derived.inv.app N) ≫
        (D.pull F L k j).derived.inv.app ((D.scalars E F h Z).T.obj N) =
      (D.pull E L (h.trans k) j).derived.inv.app N ≫ rL.map (az.inv.app N) := by
    exact inverse_path
      ((D.pull F L k j).derived.app ((D.scalars E F h Z).T.obj N))
      ((D.scalars F L k X).T.mapIso ((D.pull E F h j).derived.app N))
      (ax.app (rE.obj N)) (rL.mapIso (az.app N))
      ((D.pull E L (h.trans k) j).derived.app N)
      (by simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.comp_obj, Iso.app_hom, Functor.mapIso_hom, ax, az, rE, rL]
        using congr_app hc N)
  have hp := inverseMate_pasting
    ((D.operations E).openOp j).derivedAdjunction
    ((D.operations F).openOp j).derivedAdjunction
    ((D.operations L).openOp j).derivedAdjunction
    (D.pull E F h j).derived.inv (D.pull F L k j).derived.inv
    (D.pull E L (h.trans k) j).derived.inv ax.inv az.inv hi M
  change (SpTowerShriek.openD P.coefficients.l L.val (D.base L)
      ((D.operations L).openOp j)).map (ax.inv.app M) ≫
    (((mateEquiv ((D.operations F).openOp j).derivedAdjunction
      ((D.operations L).openOp j).derivedAdjunction).symm
        (D.pull F L k j).derived.inv).natTrans).app ((D.scalars E F h X).T.obj M) ≫
    (D.scalars F L k Z).T.map
      ((((mateEquiv ((D.operations E).openOp j).derivedAdjunction
        ((D.operations F).openOp j).derivedAdjunction).symm
          (D.pull E F h j).derived.inv).natTrans).app M) =
    (((mateEquiv ((D.operations E).openOp j).derivedAdjunction
      ((D.operations L).openOp j).derivedAdjunction).symm
        (D.pull E L (h.trans k) j).derived.inv).natTrans).app M ≫
    az.inv.app ((SpTowerShriek.openD P.coefficients.l E.val (D.base E)
      ((D.operations E).openOp j)).obj M) at hp
  rw [← congr_app (D.open_unit F L k j) ((D.scalars E F h X).T.obj M),
    ← congr_app (D.open_unit E F h j) M,
    ← congr_app (D.open_unit E L (h.trans k) j) M] at hp
  have hh := inverse_path
    ((SpTowerShriek.openD P.coefficients.l L.val (D.base L)
      ((D.operations L).openOp j)).mapIso (ax.symm.app M))
    ((D.openIso F L k j).symm.app ((D.scalars E F h X).T.obj M))
    ((D.scalars F L k Z).T.mapIso ((D.openIso E F h j).symm.app M))
    ((D.openIso E L (h.trans k) j).symm.app M)
    (az.symm.app ((SpTowerShriek.openD P.coefficients.l E.val (D.base E)
      ((D.operations E).openOp j)).obj M)) hp
  exact hh

private theorem open_identity (P : PurityFiniteSetting.{u}) (D : Models P)
    (cc : CoefficientLaws P D) (E : Index P)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : SpTowerShriek.D P.coefficients.l E.val X) :
    (D.openIso E E le_rfl j).hom.app M ≫
      (SpTowerShriek.openD P.coefficients.l E.val (D.base E)
        ((D.operations E).openOp j)).map
        ((scalarUnit P D E X (cc.identity E X)).hom.app M) =
    (scalarUnit P D E Z (cc.identity E Z)).hom.app
      ((SpTowerShriek.openD P.coefficients.l E.val (D.base E)
        ((D.operations E).openOp j)).obj M) := by
  let ax := scalarUnit P D E X (cc.identity E X)
  let az := scalarUnit P D E Z (cc.identity E Z)
  let r := SpTowerShriek.pull P.coefficients.l E.val (D.base E) ((D.operations E).geometry j)
  let l := SpTowerShriek.openD P.coefficients.l E.val (D.base E) ((D.operations E).openOp j)
  have hc := (field_shriek_system_pullback_cocycle P D E E E le_rfl le_rfl j
    (cc.composition E E E le_rfl le_rfl X) (cc.composition E E E le_rfl le_rfl Z)
    (cc.identity E X) (cc.identity E Z)).2
  have hi (N : SpTowerShriek.D P.coefficients.l E.val Z) :
      ax.inv.app (r.obj N) ≫ (D.pull E E le_rfl j).derived.inv.app N =
        r.map (az.inv.app N) := by
    have hh := inverse_path ((D.pull E E le_rfl j).derived.app N)
      (ax.app (r.obj N)) (Iso.refl _) (r.mapIso (az.app N)) (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id, NatTrans.comp_app,
        whiskerLeft_app, whiskerRight_app, Functor.comp_obj, Iso.app_hom,
        Functor.mapIso_hom, ax, az, r] using congr_app hc N)
    simp only [Iso.refl_inv, Iso.app_inv, Functor.mapIso_inv] at hh
    exact (Category.id_comp _).symm.trans (hh.trans (Category.id_comp _))
  have hp := inverseMate_unit ((D.operations E).openOp j).derivedAdjunction
    (D.pull E E le_rfl j).derived.inv ax.inv az.inv hi M
  change l.map (ax.inv.app M) ≫
    (((mateEquiv ((D.operations E).openOp j).derivedAdjunction
      ((D.operations E).openOp j).derivedAdjunction).symm
        (D.pull E E le_rfl j).derived.inv).natTrans).app M = az.inv.app (l.obj M) at hp
  rw [← congr_app (D.open_unit E E le_rfl j) M] at hp
  have he : l.mapIso (ax.symm.app M) ≪≫ (D.openIso E E le_rfl j).symm.app M =
      az.symm.app (l.obj M) := Iso.ext hp
  have hh := congrArg Iso.inv he
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv] using hh


/-- The normalized proper/open comparison satisfies composition and identity before
finite evaluation. No finite comparison or invertibility is asserted here.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
lem-sp-field-shriek-system-comparison, steps 5--7
(blueprint: lem-route-field-shriek-system-cocycle).

Proof: `field_shriek_system_coefficient_laws` gives the composition and identity of the
actual coefficient maps, hence the two coefficient fields of `CoherenceLaw`. With them,
`field_shriek_system_pullback_cocycle` gives the composition and identity equations of the
derived pullback comparisons, with the scalar associators and unitors `scalarAssoc` and
`scalarUnit`. Proper factor: the proper comparison is the mate of the pullback comparison;
whiskering a two-square whiskers its mate, and Mathlib's `mateEquiv_vcomp` pastes the two
successive mates, so the pullback cocycle gives the proper cocycle and its identity case.
Open factor: by `Models.open_unit` the inverse open comparison is the inverse mate of the
inverse pullback comparison; inverting the pullback cocycle objectwise and applying
`inverseMate_pasting` (and, for the identity, unit naturality and the adjunction Hom
bijection) gives the inverse open equations, which are then inverted. Finally the comparison
is the proper mate followed by the proper image of the open map: naturality of the second
proper mate moves the first open map past it, functoriality combines the proper images, and
substituting the open and then the proper cocycle gives the composition field; the same
expansion with the two unit equations gives the identity field. Both hold for every input,
in particular for normalized ones. No equality is inferred from finite evaluations. -/
theorem field_shriek_system_cocycle (P : PurityFiniteSetting.{u}) (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Nonempty (CoherenceLaw P D c) := by
  obtain ⟨cc⟩ := field_shriek_system_coefficient_laws P D
  refine ⟨{ coefficientComposition := cc.composition
            coefficientIdentity := cc.identity
            composition := ?_
            identity := ?_ }⟩
  · intro E F L h k M _
    exact comparison_paste
      (SpTowerShriek.openD P.coefficients.l E.val (D.base E) ((D.operations E).openOp c.i))
      (SpTowerShriek.openD P.coefficients.l F.val (D.base F) ((D.operations F).openOp c.i))
      (SpTowerShriek.openD P.coefficients.l L.val (D.base L) ((D.operations L).openOp c.i))
      (SpTowerShriek.push P.coefficients.l E.val (D.base E) ((D.operations E).geometry c.g))
      (SpTowerShriek.push P.coefficients.l F.val (D.base F) ((D.operations F).geometry c.g))
      (SpTowerShriek.push P.coefficients.l L.val (D.base L) ((D.operations L).geometry c.g))
      (D.scalars E F h X).T (D.scalars F L k X).T (D.scalars E L (h.trans k) X).T
      (D.scalars E F h c.Z).T (D.scalars F L k c.Z).T (D.scalars E L (h.trans k) c.Z).T
      (D.scalars E F h Y).T (D.scalars F L k Y).T (D.scalars E L (h.trans k) Y).T
      (scalarAssoc P D h k X (cc.composition E F L h k X)).hom
      (scalarAssoc P D h k c.Z (cc.composition E F L h k c.Z)).hom
      (scalarAssoc P D h k Y (cc.composition E F L h k Y)).hom
      (D.openIso E F h c.i).hom (D.openIso F L k c.i).hom
      (D.openIso E L (h.trans k) c.i).hom
      (proper P D h c.g) (proper P D k c.g) (proper P D (h.trans k) c.g)
      (open_composition P D cc E F L h k c.i)
      (proper_composition P D cc E F L h k c.g) M
  · intro E M _
    change ((proper P D (E := E) (F := E) le_rfl c.g).app _ ≫
        (SpTowerShriek.push P.coefficients.l E.val (D.base E)
          ((D.operations E).geometry c.g)).map ((D.openIso E E le_rfl c.i).hom.app M)) ≫
        (SpTowerShriek.push P.coefficients.l E.val (D.base E)
          ((D.operations E).geometry c.g)).map
          ((SpTowerShriek.openD P.coefficients.l E.val (D.base E)
            ((D.operations E).openOp c.i)).map
              ((scalarUnit P D E X (cc.identity E X)).hom.app M)) = _
    rw [Category.assoc, ← Functor.map_comp, open_identity P D cc E c.i M]
    exact proper_identity P D cc E c.g _


end AlgebraicGeometry.ProEtale.FieldShriekSystem
