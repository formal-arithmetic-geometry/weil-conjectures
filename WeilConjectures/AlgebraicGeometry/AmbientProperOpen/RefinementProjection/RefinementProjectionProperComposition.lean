/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionWords
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat

/-! # RefinementProjectionProperComposition

Source: blueprint fix-prop-projection-formula.proof.md, composition/refinement sentence;
Stacks 0DV0 and 0B56 (blueprint: lem-sf-refinement-projection-proper-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection

private theorem projection_composition
    {B C Y : Type*} [Category B] [Category C] [Category Y]
    {P : Y ⥤ C} {R : C ⥤ Y} {Q : C ⥤ B} {S : B ⥤ C}
    {H : Y ⥤ B} {V : B ⥤ Y}
    (adj : P ⊣ R) (adj' : Q ⊣ S) (adjH : H ⊣ V)
    (TB : B ⥤ B ⥤ B) (TC : C ⥤ C ⥤ C) (TY : Y ⥤ Y ⥤ Y)
    (t : (Functor.postcompose₂.obj P).obj TY ⟶
      (((Functor.whiskeringLeft₂ C).obj P).obj P).obj TC)
    (q : (Functor.postcompose₂.obj Q).obj TC ⟶
      (((Functor.whiskeringLeft₂ B).obj Q).obj Q).obj TB)
    (h : (Functor.postcompose₂.obj H).obj TY ⟶
      (((Functor.whiskeringLeft₂ B).obj H).obj H).obj TB)
    (e : H ≅ P ⋙ Q)
    (he : ∀ M N, e.hom.app ((TY.obj M).obj N) ≫
      Q.map ((t.app M).app N) ≫ (q.app (P.obj M)).app (P.obj N) =
      (h.app M).app N ≫ (TB.map (e.hom.app M)).app (H.obj N) ≫
        (TB.obj (Q.obj (P.obj M))).map (e.hom.app N))
    (M : B) (L : Y) :
    ((adj.rightAdjointProjectionMap t).app (S.obj M)).app L ≫
      R.map (((adj'.rightAdjointProjectionMap q).app M).app (P.obj L)) ≫
      (conjugateIsoEquiv (adj.comp adj') adjH e).hom.app
        ((TB.obj M).obj (Q.obj (P.obj L))) ≫
      V.map ((TB.obj M).map (e.inv.app L)) =
    (TY.map ((conjugateIsoEquiv (adj.comp adj') adjH e).hom.app M)).app L ≫
      ((adjH.rightAdjointProjectionMap h).app M).app L := by
  let tq : (Functor.postcompose₂.obj (P ⋙ Q)).obj TY ⟶
      (((Functor.whiskeringLeft₂ B).obj (P ⋙ Q)).obj (P ⋙ Q)).obj TB :=
    { app M := { app N := Q.map ((t.app M).app N) ≫
                    (q.app (P.obj M)).app (P.obj N)
                 naturality := by
                   intro N N' v
                   dsimp
                   have ht := (t.app M).naturality v
                   change P.map ((TY.obj M).map v) ≫ (t.app M).app N' =
                     (t.app M).app N ≫ (TC.obj (P.obj M)).map (P.map v) at ht
                   rw [← Q.map_comp_assoc, ht, Q.map_comp]
                   simp only [Category.assoc]
                   have hq := (q.app (P.obj M)).naturality (P.map v)
                   dsimp at hq
                   rw [hq] }
      naturality := by
        intro M M' v
        ext N
        dsimp
        have ht := NatTrans.congr_app (t.naturality v) N
        change P.map ((TY.map v).app N) ≫ (t.app M').app N =
          (t.app M).app N ≫ (TC.map (P.map v)).app (P.obj N) at ht
        rw [← Q.map_comp_assoc, ht, Q.map_comp]
        simp only [Category.assoc]
        have hq := NatTrans.congr_app (q.naturality (P.map v)) (P.obj N)
        dsimp at hq
        rw [hq] }
  have hc := (adj.comp adj').rightAdjointProjectionMap_conjugate tq adjH h e.hom
    (fun A B ↦ he A B) M L
  rw [Adjunction.rightAdjointProjectionMap_comp adj adj' t q tq (fun _ _ ↦ rfl)] at hc
  apply (cancel_mono (V.map ((TB.obj M).map (e.hom.app L)))).1
  simp only [Category.assoc, ← V.map_comp, ← (TB.obj M).map_comp,
    e.inv_hom_id_app]
  rw [(TB.obj M).map_id ((P ⋙ Q).obj L),
    V.map_id ((TB.obj M).obj ((P ⋙ Q).obj L))]
  simpa only [Functor.comp_obj, Category.assoc, Category.comp_id,
    conjugateIsoEquiv_apply_hom] using hc.symm

private theorem projection_composition_normalized
    {B C Y : Type*} [Category B] [Category C] [Category Y]
    {P : Y ⥤ C} {R : C ⥤ Y} {Q : C ⥤ B} {S : B ⥤ C}
    {H : Y ⥤ B} {V : B ⥤ Y}
    (adj : P ⊣ R) (adj' : Q ⊣ S) (adjH : H ⊣ V)
    (TB : B ⥤ B ⥤ B) (TC : C ⥤ C ⥤ C) (TY : Y ⥤ Y ⥤ Y)
    (t : (Functor.postcompose₂.obj P).obj TY ⟶
      (((Functor.whiskeringLeft₂ C).obj P).obj P).obj TC)
    (q : (Functor.postcompose₂.obj Q).obj TC ⟶
      (((Functor.whiskeringLeft₂ B).obj Q).obj Q).obj TB)
    (h : (Functor.postcompose₂.obj H).obj TY ⟶
      (((Functor.whiskeringLeft₂ B).obj H).obj H).obj TB)
    (e : H ≅ P ⋙ Q)
    (he : ∀ M N, e.hom.app ((TY.obj M).obj N) ≫
      Q.map ((t.app M).app N) ≫ (q.app (P.obj M)).app (P.obj N) =
      (h.app M).app N ≫ (TB.map (e.hom.app M)).app (H.obj N) ≫
        (TB.obj (Q.obj (P.obj M))).map (e.hom.app N))
    (M : B) (L : Y) :
    ((adj.rightAdjointProjectionMap t).app (S.obj M)).app L ≫
      R.map (((adj'.rightAdjointProjectionMap q).app M).app (P.obj L) ≫
        S.map ((TB.obj M).map (e.inv.app L))) ≫
      (conjugateIsoEquiv (adj.comp adj') adjH e).hom.app
        ((TB.obj M).obj (H.obj L)) =
    (TY.map ((conjugateIsoEquiv (adj.comp adj') adjH e).hom.app M)).app L ≫
      ((adjH.rightAdjointProjectionMap h).app M).app L := by
  rw [R.map_comp, Category.assoc]
  have hn := (conjugateIsoEquiv (adj.comp adj') adjH e).hom.naturality
    ((TB.obj M).map (e.inv.app L))
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  exact projection_composition adj adj' adjH TB TC TY t q h e he M L

private theorem projection_composition_transport
    {I B C Y : Type*} [catB : Category B] [catC : Category C] [catY : Category Y]
    (Pbar : I → Y ⥤ B) (Vbar : I → B ⥤ Y)
    {P : Y ⥤ C} {R : C ⥤ Y} {Q : C ⥤ B} {S : B ⥤ C}
    (adj : P ⊣ R) (adj' : Q ⊣ S) (adjbar : ∀ i, Pbar i ⊣ Vbar i)
    (TB : B ⥤ B ⥤ B) (TC : C ⥤ C ⥤ C) (TY : Y ⥤ Y ⥤ Y)
    (t : (Functor.postcompose₂.obj P).obj TY ⟶
      (((Functor.whiskeringLeft₂ C).obj P).obj P).obj TC)
    (q : (Functor.postcompose₂.obj Q).obj TC ⟶
      (((Functor.whiskeringLeft₂ B).obj Q).obj Q).obj TB)
    (tbar : ∀ i, (Functor.postcompose₂.obj (Pbar i)).obj TY ⟶
      (((Functor.whiskeringLeft₂ B).obj (Pbar i)).obj (Pbar i)).obj TB)
    {i j : I} (hij : i = j) (e : Pbar i ≅ P ⋙ Q)
    (he : ∀ M N, e.hom.app ((TY.obj M).obj N) ≫
      Q.map ((t.app M).app N) ≫ (q.app (P.obj M)).app (P.obj N) =
      ((tbar i).app M).app N ≫ (TB.map (e.hom.app M)).app ((Pbar i).obj N) ≫
        (TB.obj (Q.obj (P.obj M))).map (e.hom.app N))
    (M : B) (L : Y) :
    ((adj.rightAdjointProjectionMap t).app (S.obj M)).app L ≫
      R.map (((adj'.rightAdjointProjectionMap q).app M).app (P.obj L) ≫
        S.map ((TB.obj M).map (e.inv.app L ≫
          (indexIso Pbar hij).hom.app L))) ≫
      ((conjugateIsoEquiv (adj.comp adj') (adjbar i) e).hom.app
        ((TB.obj M).obj ((Pbar j).obj L)) ≫
        (indexIso Vbar hij).hom.app ((TB.obj M).obj ((Pbar j).obj L))) =
    (TY.map ((conjugateIsoEquiv (adj.comp adj') (adjbar i) e).hom.app M ≫
        (indexIso Vbar hij).hom.app M)).app L ≫
      (((adjbar j).rightAdjointProjectionMap (tbar j)).app M).app L := by
  cases hij
  simp only [indexIso, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  exact projection_composition_normalized adj adj' (adjbar i)
    TB TC TY t q (tbar i) e he M L

set_option backward.defeqAttrib.useBackward false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem system_comp
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : WeilConjectures.IntegralSystemRealization.Operations l E)
    (c : WeilConjectures.IntegralSystemRealization.Compositors l E o)
    {B C Y : Scheme.{u}} (v : B ⟶ C) (p : C ⟶ Y)
    (ht : ∀ M N,
      (c.pullComp v p).hom.app
        ((WeilConjectures.IntegralSystemRealization.calculus l E Y).systemClosed.tensor.obj
          (M, N)) ≫
      (WeilConjectures.IntegralSystemRealization.pull l E v).map
        ((WeilConjectures.pullbackTensorSystemComparison l E p).hom.app (M, N)) ≫
      (WeilConjectures.pullbackTensorSystemComparison l E v).hom.app
        ((WeilConjectures.IntegralSystemRealization.pull l E p).obj M,
          (WeilConjectures.IntegralSystemRealization.pull l E p).obj N) =
      (WeilConjectures.pullbackTensorSystemComparison l E (v ≫ p)).hom.app (M, N) ≫
        (WeilConjectures.IntegralSystemRealization.calculus l E B).systemClosed.tensor.map
          (Prod.mkHom ((c.pullComp v p).hom.app M) ((c.pullComp v p).hom.app N)))
    (q : B ⟶ Y) (hq : v ≫ p = q)
    (M : WeilConjectures.IntegralSystemRealization.System l E B)
    (L : WeilConjectures.IntegralSystemRealization.System l E Y) :
    let R := WeilConjectures.IntegralSystemRealization.Operations.push l E o p
    let S := WeilConjectures.IntegralSystemRealization.Operations.push l E o v
    let P := WeilConjectures.IntegralSystemRealization.pull l E p
    let H := WeilConjectures.IntegralSystemRealization.pull l E q
    let TB := (WeilConjectures.IntegralSystemRealization.calculus l E B).systemClosed.tensor
    let TY := (WeilConjectures.IntegralSystemRealization.calculus l E Y).systemClosed.tensor
    let cc := (c.pushComp l E v p).hom ≫
      (eqToIso (congrArg
        (fun g : B ⟶ Y ↦ WeilConjectures.IntegralSystemRealization.Operations.push l E o g)
        hq)).hom
    ((WeilConjectures.IntegralSystemRealization.properProjection l E o p).app
        (S.obj M)).app L ≫
      R.map (((WeilConjectures.IntegralSystemRealization.properProjection l E o v).app
        M).app (P.obj L) ≫ S.map (TB.map (Prod.mkHom (𝟙 M)
          ((c.pullComp v p).inv.app L ≫
            eqToHom (congrArg
              (fun g ↦ (WeilConjectures.IntegralSystemRealization.pull l E g).obj L) hq))))) ≫
      cc.app (TB.obj (M, H.obj L)) =
    TY.map (Prod.mkHom (cc.app M) (𝟙 L)) ≫
      ((WeilConjectures.IntegralSystemRealization.properProjection l E o q).app M).app L := by
  dsimp only
  subst q
  simp only [eqToIso_refl, Iso.refl_hom,
    eqToHom_refl, Category.comp_id]
  have h := projection_composition_normalized
    (o.direct p).adj (o.direct v).adj (o.direct (v ≫ p)).adj
    (Functor.curryObj
      (WeilConjectures.IntegralSystemRealization.calculus l E B).systemClosed.tensor)
    (Functor.curryObj
      (WeilConjectures.IntegralSystemRealization.calculus l E C).systemClosed.tensor)
    (Functor.curryObj
      (WeilConjectures.IntegralSystemRealization.calculus l E Y).systemClosed.tensor)
    (Functor.curry.mapIso (WeilConjectures.pullbackTensorSystemComparison l E p) ≪≫
      Functor.curryObjProdComp _ _ _).hom
    (Functor.curry.mapIso (WeilConjectures.pullbackTensorSystemComparison l E v) ≪≫
      Functor.curryObjProdComp _ _ _).hom
    (Functor.curry.mapIso (WeilConjectures.pullbackTensorSystemComparison l E (v ≫ p)) ≪≫
      Functor.curryObjProdComp _ _ _).hom
    (c.pullComp v p) (by
      intro N N'
      dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom,
        Functor.curry_map_app_app, Functor.curryObjProdComp_hom_app_app]
      erw [Category.comp_id, Category.comp_id, Category.comp_id]
      dsimp only [CategoryTheory.Functor.curryObj]
      rw [← (WeilConjectures.IntegralSystemRealization.calculus l E B).systemClosed.tensor.map_comp]
      simp only [CategoryTheory.prod_comp]
      erw [Category.comp_id, Category.id_comp]
      exact ht N N') M L
  exact h

section FiniteProof

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.mapDerivedCategory
  leftDerivedUpperStarComp leftDerivedUpperStarTensorNatIso
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarTensorComparison derivedTensor

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory

private theorem proper_projection_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B Y : Scheme.{u}} (p : B ⟶ Y)
    (M : ProperOpenDerived A B) (L : ProperOpenDerived A Y) :
    properOpenProjection A p M L =
      (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).rightAdjointProjectionMap
        (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) p)).app M).app L := by
  rfl

private theorem tensor_component_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B Y : Scheme.{u}} (p : B ⟶ Y)
    (M N : ProperOpenDerived A Y) :
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) p M N).hom =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) p).app M).app N := by
  exact leftDerivedUpperStarTensorIso_hom (ModuleCat.{u + 1} A) p M N

private theorem tensor_comp_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B C Y : Scheme.{u}} (v : B ⟶ C) (p : C ⟶ Y)
    (ht : ∀ M N,
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app
        (((ProperOpenTensor A Y).obj M).obj N) ≫
      (ProperOpenPull A v).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) p M N).hom ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v
        ((ProperOpenPull A p).obj M) ((ProperOpenPull A p).obj N)).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (v ≫ p) M N).hom ≫
      ((ProperOpenTensor A B).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app M)).app
          ((ProperOpenPull A (v ≫ p)).obj N) ≫
      ((ProperOpenTensor A B).obj
        ((ProperOpenPull A v).obj ((ProperOpenPull A p).obj M))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app N))
    : ∀ V W,
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app
        (((ProperOpenTensor A Y).obj V).obj W) ≫
      (ProperOpenPull A v).map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) p).app V).app W) ≫
      (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) v).app
        ((ProperOpenPull A p).obj V)).app ((ProperOpenPull A p).obj W)) =
      (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) (v ≫ p)).app V).app W) ≫
      ((ProperOpenTensor A B).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app V)).app
          ((ProperOpenPull A (v ≫ p)).obj W) ≫
      ((ProperOpenTensor A B).obj
        ((ProperOpenPull A v).obj ((ProperOpenPull A p).obj V))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app W) := by
  intro V W
  let d := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom
  let P := ProperOpenPull A p
  let Q := ProperOpenPull A v
  let TB := ProperOpenTensor A B
  let TY := ProperOpenTensor A Y
  have hp := tensor_component_hom A p V W
  have hv := tensor_component_hom A v (P.obj V) (P.obj W)
  have hc := tensor_component_hom A (v ≫ p) V W
  calc
    _ = d.app ((TY.obj V).obj W) ≫
        Q.map (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) p V W).hom ≫
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v
            (P.obj V) (P.obj W)).hom :=
      congrArg₂ (fun a b ↦ d.app ((TY.obj V).obj W) ≫ Q.map a ≫ b)
        hp.symm hv.symm
    _ = (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (v ≫ p) V W).hom ≫
        (TB.map (d.app V)).app ((ProperOpenPull A (v ≫ p)).obj W) ≫
          (TB.obj (Q.obj (P.obj V))).map (d.app W) := ht V W
    _ = _ := congrArg (fun a ↦ a ≫
      (TB.map (d.app V)).app ((ProperOpenPull A (v ≫ p)).obj W) ≫
        (TB.obj (Q.obj (P.obj V))).map (d.app W)) hc

private theorem finite_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B C Y : Scheme.{u}} (v : B ⟶ C) (p : C ⟶ Y)
    (ht : ∀ M N,
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app
        (((ProperOpenTensor A Y).obj M).obj N) ≫
      (ProperOpenPull A v).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) p M N).hom ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v
        ((ProperOpenPull A p).obj M) ((ProperOpenPull A p).obj N)).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (v ≫ p) M N).hom ≫
      ((ProperOpenTensor A B).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app M)).app
          ((ProperOpenPull A (v ≫ p)).obj N) ≫
      ((ProperOpenTensor A B).obj
        ((ProperOpenPull A v).obj ((ProperOpenPull A p).obj M))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).hom.app N))
    (q : B ⟶ Y) (hq : v ≫ p = q) (M : ProperOpenDerived A B)
    (L : ProperOpenDerived A Y) :
    properOpenProjection A p ((ProperOpenPush A v).obj M) L ≫
      (ProperOpenPush A p).map (properOpenProjection A v M
        ((ProperOpenPull A p).obj L) ≫ (ProperOpenPush A v).map
        (((ProperOpenTensor A B).obj M).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).inv.app L ≫
            (indexIso (ProperOpenPull A) hq).hom.app L))) ≫
      ((conjugateIsoEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (v ≫ p))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p)).hom.app
        (((ProperOpenTensor A B).obj M).obj ((ProperOpenPull A q).obj L)) ≫
        (indexIso (ProperOpenPush A) hq).hom.app
          (((ProperOpenTensor A B).obj M).obj ((ProperOpenPull A q).obj L))) =
      ((ProperOpenTensor A Y).map
        ((conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).comp
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (v ≫ p))
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p)).hom.app M ≫
          (indexIso (ProperOpenPush A) hq).hom.app M)).app L ≫
        properOpenProjection A q M L := by
  rw [proper_projection_eq, proper_projection_eq, proper_projection_eq]
  have h := projection_composition_transport
    (I := B ⟶ Y)
    (catB := (inferInstance : Category.{u + 1} (ProperOpenDerived A B)))
    (catC := (inferInstance : Category.{u + 1} (ProperOpenDerived A C)))
    (catY := (inferInstance : Category.{u + 1} (ProperOpenDerived A Y)))
    (B := ProperOpenDerived A B) (C := ProperOpenDerived A C)
    (Y := ProperOpenDerived A Y)
    (ProperOpenPull A) (ProperOpenPush A)
    (P := ProperOpenPull A p) (R := ProperOpenPush A p)
    (Q := ProperOpenPull A v) (S := ProperOpenPush A v)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)
    (fun q ↦ derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (ProperOpenTensor A B) (ProperOpenTensor A C) (ProperOpenTensor A Y)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) p)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) v)
    (fun q ↦ (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) q))
    hq (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p)
    (tensor_comp_eq A v p ht) M L
  exact h

private def ambientSpace (F : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Spaces F} {f : X ⟶ Y} (c : Compactification f.hom.left) : Spaces F := by
  letI := Y.property.1
  letI := Y.property.2
  refine ⟨Over.mk (c.g ≫ Y.obj.hom), ?_, ?_⟩
  · change LocallyOfFiniteType (c.g ≫ Y.obj.hom)
    infer_instance
  · change QuasiCompact (c.g ≫ Y.obj.hom)
    infer_instance

/-- Stacks 0DV0 and 0B56, the composition part of the refinement calculation.
(blueprint: lem-sf-refinement-projection-proper-composition).

Proof: The transpose of proper projection is tensor comparison followed by counit
tensored with identity. Transpose successive projections under the composite
adjunction. Naturality of the tensor comparison and the formula for the composite
counit identify that transpose with the projection for the composite. The canonical
pullback compositor respects tensor by ambientProperOpenPasting. Apply the conjugate
comparison identity and naturality to move its inverse pullback component inside the
successive pushforwards. Finally transport along u followed by p2 equals p1. This is
the displayed Composition equation. The same calculation uses the actual system
adjunctions and the supplied system tensor-composition equation before evaluation.
-/
theorem refinementProjectionProperComposition
    (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (r : c₁.Refinement c₂) :
    Words.Composition (finiteWords F
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) r) ∧
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
      (z : WeilConjectures.IntegralSystemRealization.Realizations l E F o),
      Words.Composition (WeilConjectures.IntegralSystemRealization.RefinementProjection.systemWords
        l E F o z r) := by
  constructor
  · let B := ambientSpace F (f := f) c₁
    let C := ambientSpace F (f := f) c₂
    let v : B ⟶ C := ObjectProperty.homMk (Over.homMk r.hom (by
      change r.hom ≫ (c₂.g ≫ Y.obj.hom) = c₁.g ≫ Y.obj.hom
      rw [← Category.assoc, r.hom_g]))
    let p : C ⟶ Y := ObjectProperty.homMk (Over.homMk c₂.g rfl)
    unfold Words.Composition finiteWords
    intro M L
    have ht := (ambientProperOpenPasting F l _hl E n).2.1 v p
    dsimp +instances only [ordinary] at ht
    exact finite_comp
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) r.hom c₂.g
      ht c₁.g r.hom_g M L
  · intro o z
    let B := ambientSpace F (f := f) c₁
    let C := ambientSpace F (f := f) c₂
    let v : B ⟶ C := ObjectProperty.homMk (Over.homMk r.hom (by
      change r.hom ≫ (c₂.g ≫ Y.obj.hom) = c₁.g ≫ Y.obj.hom
      rw [← Category.assoc, r.hom_g]))
    let p : C ⟶ Y := ObjectProperty.homMk (Over.homMk c₂.g rfl)
    unfold Words.Composition
      WeilConjectures.IntegralSystemRealization.RefinementProjection.systemWords
    intro M L
    have ht := (ambientProperOpenPasting F l _hl E n).2.2.2 o z.compositors v p
    exact system_comp l E o z.compositors r.hom c₂.g ht c₁.g r.hom_g M L

end FiniteProof

end AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection
