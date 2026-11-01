/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.ProperCoordinates.IntegralProperProjectionCoefficientData
import WeilConjectures.SixFunctors.IntegralSystemRealization.SystemPushIdentityPullUnit
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCompositorAssociativity
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemTensorComposition
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionWords

/-! # Proper projection and identity-open cancellation on systems

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Functor
namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization
open FixProjectionCompactification.Coordinates
open ProperCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

open AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_identity_unit
    {C : Type*} [Category C] (T : C × C ⥤ C) (U : C ⥤ C)
    (e : U ≅ 𝟭 C) (c : U ≅ U ⋙ U)
    (t : T ⋙ U ⟶ (U.prod U) ⋙ T)
    [IsIso t]
    (hc : ∀ M, c.hom.app M ≫ U.map (e.hom.app M) = 𝟙 _)
    (ht : ∀ M N, c.hom.app (T.obj (M, N)) ≫ U.map (t.app (M, N)) ≫
      t.app (U.obj M, U.obj N) =
      t.app (M, N) ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app N)))
    (M N : C) :
    t.app (M, N) ≫ T.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (T.obj (M, N)) := by
  let : U.Faithful := Functor.Faithful.of_iso e.symm
  apply U.map_injective
  apply (cancel_epi (c.hom.app (T.obj (M, N)))).1
  apply (cancel_mono (t.app (M, N))).1
  have hn := t.naturality (Prod.mkHom (e.hom.app M) (e.hom.app N))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_obj] at hn
  simp only [U.map_comp, Category.assoc]
  rw [hn, reassoc_of% (ht M N)]
  simp only [← T.map_comp, CategoryTheory.prod_comp, hc]
  change t.app (M, N) ≫ T.map (𝟙 _) = _
  rw [T.map_id]
  erw [Category.comp_id, ← Category.assoc, hc, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_identity_unit_index
    {I C : Type*} [Category C] (T : C × C ⥤ C) (U : I → C ⥤ C)
    (t : ∀ i, T ⋙ U i ≅ ((U i).prod (U i)) ⋙ T)
    {i j : I} (h : i = j) (e : U j ≅ 𝟭 C) (c : U i ≅ U j ⋙ U j)
    (hc : ∀ M, (indexIso U h.symm).hom.app M ≫
      c.hom.app M ≫ (U j).map (e.hom.app M) = 𝟙 _)
    (ht : ∀ M N, c.hom.app (T.obj (M, N)) ≫ (U j).map ((t j).hom.app (M, N)) ≫
      (t j).hom.app ((U j).obj M, (U j).obj N) =
      (t i).hom.app (M, N) ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app N)))
    (M N : C) :
    (t j).hom.app (M, N) ≫ T.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (T.obj (M, N)) := by
  cases h
  simp only [indexIso, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hc
  exact tensor_identity_unit T (U i) e c (t i).hom hc ht M N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_comp_congr_left
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X Y Z : G} {f f' : X ⟶ Y} (h : f = f') (g : Y ⟶ Z) (M : D Z) :
    (indexIso P (congrArg (· ≫ g) h)).hom.app M ≫ (c f' g).hom.app M =
      (c f g).hom.app M ≫ (indexIso P h).hom.app ((P g).obj M) := by
  cases h
  simp [indexIso]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_comp_congr_right
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X Y Z : G} (f : X ⟶ Y) {g g' : Y ⟶ Z} (h : g = g') (M : D Z) :
    (indexIso P (congrArg (f ≫ ·) h)).hom.app M ≫ (c f g').hom.app M =
      (c f g).hom.app M ≫ (P f).map ((indexIso P h).hom.app M) := by
  cases h
  simp [indexIso]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem indexIso_trans_app
    {I C D : Type*} [Category C] [Category D] (P : I → C ⥤ D)
    {i j k : I} (h : i = j) (h' : j = k) (M : C) :
    (indexIso P h).hom.app M ≫ (indexIso P h').hom.app M =
      (indexIso P (h.trans h')).hom.app M := by
  cases h
  cases h'
  simp [indexIso]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_left_unit
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X : G} (e : P (𝟙 X) ≅ 𝟭 (D X))
    (he : ∀ M, (indexIso P (Category.id_comp (𝟙 X)).symm).hom.app M ≫
      (c (𝟙 X) (𝟙 X)).hom.app M ≫ (P (𝟙 X)).map (e.hom.app M) = 𝟙 _)
    {Y : G} (f : X ⟶ Y) (M : D Y)
    (ha : (c (𝟙 X) ((𝟙 X) ≫ f)).hom.app M ≫
      (P (𝟙 X)).map ((c (𝟙 X) f).hom.app M) =
      (indexIso P (Category.assoc (𝟙 X) (𝟙 X) f).symm).hom.app M ≫
        (c ((𝟙 X) ≫ (𝟙 X)) f).hom.app M ≫
        (c (𝟙 X) (𝟙 X)).hom.app ((P f).obj M)) :
    (indexIso P (Category.id_comp f).symm).hom.app M ≫ (c (𝟙 X) f).hom.app M ≫
      e.hom.app ((P f).obj M) = 𝟙 _ := by
  let U := P (𝟙 X)
  let k := indexIso P (Category.id_comp f).symm ≪≫ c (𝟙 X) f
  let ci := indexIso P (Category.id_comp (𝟙 X)).symm ≪≫ c (𝟙 X) (𝟙 X)
  have hk : k.hom.app M ≫ U.map (k.hom.app M) =
      k.hom.app M ≫ ci.hom.app ((P f).obj M) := by
    dsimp only [k, ci, Iso.trans_hom, NatTrans.comp_app]
    simp only [U, Functor.map_comp, Category.assoc]
    rw [← reassoc_of% (pull_comp_congr_right D P c (𝟙 X) (Category.id_comp f).symm M)]
    rw [ha]
    have hl := pull_comp_congr_left D P c (Category.id_comp (𝟙 X)).symm f M
    rw [← reassoc_of% hl]
    simp only [← Category.assoc, indexIso_trans_app]
  have hh := (cancel_epi (k.hom.app M)).1 hk
  let : U.Faithful := Functor.Faithful.of_iso e.symm
  have hz : U.map (k.hom.app M ≫ e.hom.app ((P f).obj M)) = U.map (𝟙 _) := by
    rw [U.map_comp, hh, U.map_id]
    simpa only [ci, U, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
      using he ((P f).obj M)
  have hz' := U.map_injective hz
  simpa only [k, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using hz'

private theorem identity_iso_map' {C : Type*} [Category C]
    {U : C ⥤ C} (e : U ≅ 𝟭 C) (M : C) :
    U.map (e.hom.app M) = e.hom.app (U.obj M) := by
  apply (cancel_mono (e.hom.app M)).1
  exact e.hom.naturality (e.hom.app M)

private theorem pull_unit_app
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X : G} (e : P (𝟙 X) ≅ 𝟭 (D X))
    (h : eqToIso (congrArg P (Category.id_comp (𝟙 X)).symm) ≪≫
      c (𝟙 X) (𝟙 X) ≪≫ Functor.isoWhiskerLeft (P (𝟙 X)) e ≪≫
        Functor.rightUnitor (P (𝟙 X)) = Iso.refl _) (M : D X) :
    (indexIso P (Category.id_comp (𝟙 X)).symm).hom.app M ≫
      (c (𝟙 X) (𝟙 X)).hom.app M ≫ (P (𝟙 X)).map (e.hom.app M) = 𝟙 _ := by
  have hh := congrArg (fun q ↦ q.hom.app M) h
  rw [eqToIso_congrArg_indexIso P (Category.id_comp (𝟙 X)).symm] at hh
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Iso.refl_hom, NatTrans.id_app, ← identity_iso_map' e] at hh
  erw [Category.comp_id ((P (𝟙 X)).map (e.hom.app M))] at hh
  exact hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_assoc_app
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {W X Y Z : G} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (ha : c f (g ≫ h) ≪≫ Functor.isoWhiskerRight (c g h) (P f) =
      eqToIso (congrArg P (Category.assoc f g h).symm) ≪≫ c (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (P h) (c f g)) (M : D Z) :
    (c f (g ≫ h)).hom.app M ≫ (P f).map ((c g h).hom.app M) =
      (indexIso P (Category.assoc f g h).symm).hom.app M ≫
        (c (f ≫ g) h).hom.app M ≫ (c f g).hom.app ((P h).obj M) := by
  rw [eqToIso_congrArg_indexIso P (Category.assoc f g h).symm] at ha
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      using congrArg (fun q ↦ q.hom.app M) ha

private theorem indexIso_inv_app {I A B : Type*} [Category A] [Category B]
    (P : I → A ⥤ B) {i j : I} (h : i = j) (M : A) :
    (indexIso P h).inv.app M = eqToHom (congrArg (fun i ↦ (P i).obj M) h.symm) := by
  cases h
  rfl

private theorem conjugate_iso_trans
    {A B : Type*} [Category A] [Category B]
    {L₁ L₂ L₃ : A ⥤ B} {R₁ R₂ R₃ : B ⥤ A}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (e : L₂ ≅ L₁) (f : L₃ ≅ L₂) :
    conjugateIsoEquiv a₁ a₃ (f ≪≫ e) =
      conjugateIsoEquiv a₁ a₂ e ≪≫ conjugateIsoEquiv a₂ a₃ f := by
  ext : 1
  exact (conjugateEquiv_comp a₁ a₂ a₃ e.hom f.hom).symm

private theorem identity_bridge {C : Type*} [Category C]
    {F₁ F₂ G₁ G₂ : C ⥤ C} (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂)
    (b : G₁ ≅ G₂) (e : G₂ ≅ 𝟭 C) :
    Adjunction.leftAdjointIdIso a₁ (b ≪≫ e) =
      (a₁.ofNatIsoRight b).leftAdjointUniq a₂ ≪≫ Adjunction.leftAdjointIdIso a₂ e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (a₁.homEquiv X X).injective
  simp [Adjunction.leftAdjointIdIso, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv_symm_apply_inv, conjugateEquiv_symm_apply_app,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem identity_open_projection
    {A : Type*} [Category A] (T : A × A ⥤ A)
    {J P : A ⥤ A} (adj : J ⊣ P) (e : P ≅ 𝟭 A)
    (t : T ⋙ P ≅ P.prod P ⋙ T)
    (d : J.prod (𝟭 A) ⋙ T ≅ (𝟭 A).prod P ⋙ T ⋙ J)
    (ht : ∀ M N, t.hom.app (M, N) ≫
      T.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) = e.hom.app (T.obj (M, N)))
    (hd : ∀ M N, adj.homEquiv _ _ (d.inv.app (M, N)) =
      T.map (Prod.mkHom (adj.unit.app M) (𝟙 (P.obj N))) ≫ t.inv.app (J.obj M, N))
    (M N : A) :
    d.hom.app (M, N) ≫ J.map (T.map (Prod.mkHom (𝟙 M) (e.hom.app N))) ≫
        (adj.leftAdjointIdIso e).hom.app (T.obj (M, N)) =
      T.map (Prod.mkHom ((adj.leftAdjointIdIso e).hom.app M) (𝟙 N)) := by
  let j := adj.leftAdjointIdIso e
  have hu (V : A) : adj.unit.app V ≫ P.map (j.hom.app V) = e.inv.app V := by
    have h := unit_conjugateEquiv_symm Adjunction.id adj e.inv V
    simpa only [j, Adjunction.leftAdjointIdIso, conjugateIsoEquiv_symm_apply_hom,
      Iso.symm_hom, Adjunction.id_unit, NatTrans.id_app, Category.id_comp,
      Functor.id_obj] using h.symm
  have hv (V : A) : adj.unit.app V ≫ e.hom.app (J.obj V) = j.inv.app V := by
    apply (cancel_mono (j.hom.app V)).1
    simp only [Category.assoc, j.inv_hom_id_app]
    have hn := e.hom.naturality (j.hom.app V)
    dsimp only [Functor.id_map, Functor.id_obj] at hn
    rw [← hn, ← Category.assoc, hu, e.inv_hom_id_app]
  have heq {V W : A} (v : J.obj V ⟶ W) :
      adj.homEquiv V W v ≫ e.hom.app W = j.inv.app V ≫ v := by
    rw [Adjunction.homEquiv_unit, Category.assoc]
    have hn := e.hom.naturality v
    dsimp only [Functor.id_map] at hn
    rw [hn, ← Category.assoc, hv]
  have hi (V W : A) : t.inv.app (V, W) ≫ e.hom.app (T.obj (V, W)) =
      T.map (Prod.mkHom (e.hom.app V) (e.hom.app W)) := by
    apply (cancel_epi (t.hom.app (V, W))).1
    rw [t.hom_inv_id_app_assoc, ht]
  have h := congrArg (fun v ↦ v ≫ e.hom.app (T.obj (J.obj M, N))) (hd M N)
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at h
  rw [heq] at h
  simp only [Category.assoc, hi, ← T.map_comp, CategoryTheory.prod_comp,
    Category.id_comp, hv] at h
  change d.hom.app (M, N) ≫ J.map (T.map (Prod.mkHom (𝟙 M) (e.hom.app N))) ≫
    j.hom.app _ = T.map (Prod.mkHom (j.hom.app M) (𝟙 N))
  apply (cancel_epi (d.inv.app (M, N))).1
  simp only [d.inv_hom_id_app_assoc]
  rw [j.hom.naturality]
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.id_map]
  apply (cancel_epi (j.inv.app (T.obj (M, P.obj N)))).1
  simp only [← Category.assoc, j.inv_hom_id_app, Category.id_comp]
  rw [h]
  simp only [← T.map_comp, CategoryTheory.prod_comp, j.inv_hom_id_app]
  simp only [Functor.id_obj, Category.comp_id]

attribute [local irreducible] IntegralSystemRealization.properProjection
  ProperCoordinates.openIdentity pullbackTensorSystemComparison
  Functor.mapDerivedCategory Direct.adj

set_option maxHeartbeats 600000 in
-- Elaborate the tensor, compositor and adjunction normalizations in one calculation.
/-- Identity-open cancellation for the projection formed entirely on strict
coefficient systems. No integral object or integral operation datum occurs.

Source: fix-prop-projection-formula.proof.md, proper coincidence; Stacks 0E48,
the counit definition of projection and the normalized open-unit tensor map.
(blueprint: lem-sf-system-proper-identity-open-projection).

Proof: expand compactificationProjection for the identity-open compactification.
Naturality of the proper counit projection moves direct image of openIdentity
through the first tensor slot. For the remaining open tensor factor, transpose its
inverse under the open adjunction and apply projection_transpose. The identity-open
comparison is the unique adjunction comparison to the identity, so its unit is the
identity under that comparison. The canonical tensor pullback comparison for the
identity and the inverse pullback compositor cancel under their section-normalized
models. Thus the open factor followed by openIdentity on the tensor is tensor of
openIdentity and the identity on the pulled second factor. Apply proper direct
image and the preceding naturality equality. All identities hold on whole strict
systems, including quotient transitions, before derived localization. No good-system
hypothesis or faithfulness of finite evaluation is used. -/
theorem systemProperIdentityOpenProjection
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : System C.l E X) (N : System C.l E Y) :
    (calculus C.l E Y).systemClosed.tensor.map
        (Prod.mkHom ((Operations.push C.l E o f).map
          ((openIdentity o z X).hom.app M)) (𝟙 N)) ≫
        ((properProjection C.l E o f).app M).app N =
      compactificationProjection C.l E o z.compositors z.openComparisons
          (.ofIsProper f) M N ≫
        (Operations.push C.l E o f).map ((openIdentity o z X).hom.app
          ((calculus C.l E X).systemClosed.tensor.obj (M, (pull C.l E f).obj N))) := by
  dsimp only [compactificationProjection, Compactification.ofIsProper]
  let c := z.compositors
  obtain ⟨e, he, hb⟩ := systemPushIdentityPullUnit C.l E o c z.canonicalBridge X
  have he' := pull_unit_app (System C.l E) (pull C.l E) c.pullComp e he
  have ht (A B : System C.l E X) := tensor_identity_unit_index
    (calculus C.l E X).systemClosed.tensor
    (fun g : X ⟶ X ↦ pull C.l E g)
    (fun g ↦ pullbackTensorSystemComparison C.l E g)
    (Category.id_comp (𝟙 X)) e (c.pullComp (𝟙 X) (𝟙 X)) he'
    (integralSystemTensorComposition C.l E o c (𝟙 X) (𝟙 X)) A B
  have hec : e = z.canonicalBridge.pull C.l E (𝟙 X) ≪≫
      SemilinearProperOpen.pId (scalarRings C.l E) (scalarTransitions C.l E) X := by
    have hh : e.symm = (z.canonicalBridge.pull C.l E (𝟙 X) ≪≫
        SemilinearProperOpen.pId (scalarRings C.l E) (scalarTransitions C.l E) X).symm := by
      apply (conjugateIsoEquiv (o.direct (𝟙 X)).adj Adjunction.id).injective
      rw [hb, Iso.trans_symm, conjugate_iso_trans]
      rfl
    simpa only [Iso.symm_symm_eq] using congrArg Iso.symm hh
  have hj : (o.extension (𝟙 X)).adj.leftAdjointIdIso e = openIdentity o z X := by
    rw [hec]
    simpa only [openIdentity, CanonicalBridge.shriek, SemilinearProperOpen.jId] using
      identity_bridge (o.extension (𝟙 X)).adj
        (SemilinearProperOpen.jAdj (scalarRings C.l E) (scalarTransitions C.l E) (𝟙 X))
        (z.canonicalBridge.pull C.l E (𝟙 X))
        (SemilinearProperOpen.pId (scalarRings C.l E) (scalarTransitions C.l E) X)
  have ho := identity_open_projection (calculus C.l E X).systemClosed.tensor
    (o.extension (𝟙 X)).adj e (pullbackTensorSystemComparison C.l E (𝟙 X))
    (z.openComparisons.projection (𝟙 X)) ht
    (z.openComparisons.projection_transpose (𝟙 X)) M ((pull C.l E f).obj N)
  rw [hj] at ho
  have ha := integralSystemCompositorAssociativity C.l E c (𝟙 X) (𝟙 X) f
  have hf := pull_left_unit (System C.l E) (pull C.l E) c.pullComp e he' f N
    (pull_assoc_app (System C.l E) (pull C.l E) c.pullComp (𝟙 X) (𝟙 X) f ha N)
  have hf' : (c.pullComp (𝟙 X) f).inv.app N ≫
      eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull C.l E g).obj N)
        (Category.id_comp f)) = e.hom.app ((pull C.l E f).obj N) := by
    let k := indexIso (pull C.l E) (Category.id_comp f).symm ≪≫ c.pullComp (𝟙 X) f
    have hki : k.inv.app N = e.hom.app ((pull C.l E f).obj N) := by
      apply (cancel_epi (k.hom.app N)).1
      rw [k.hom_inv_id_app]
      simpa only [k, Iso.trans_hom, NatTrans.comp_app, Functor.id_obj,
        Category.assoc] using hf.symm
    simpa only [k, Iso.trans_inv, NatTrans.comp_app, indexIso_inv_app] using hki
  have hn := tensorNaturality (Operations.push C.l E o f) (pull C.l E f)
    (calculus C.l E X).systemClosed.tensor (calculus C.l E Y).systemClosed.tensor
    (properProjection C.l E o f) ((openIdentity o z X).hom.app M) N
  dsimp only [Functor.id_obj] at hn
  rw [hn]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hf']
  exact congrArg (fun v ↦
    ((properProjection C.l E o f).app ((Operations.shriek C.l E o (𝟙 X)).obj M)).app N ≫
      (Operations.push C.l E o f).map v) ho.symm

end WeilConjectures.IntegralProjectionReduction
