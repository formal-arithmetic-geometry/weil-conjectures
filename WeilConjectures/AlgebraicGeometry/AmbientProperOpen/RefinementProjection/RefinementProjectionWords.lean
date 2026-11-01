/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection

/-! # Words in the refinement projection calculation

Source: blueprint fix-prop-projection-formula.proof.md, composition/refinement sentence;
Stacks 0B56 and 0DV0 (blueprint: def-sf-refinement-projection-words).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection

/-- First-variable naturality of a curried projection transformation.
Source: naturality of the specified projection map
(blueprint: def-sf-refinement-projection-words). -/
theorem curriedNaturality {C Y : Type*} [Category C] [Category Y]
    (R : C ⥤ Y) (P : Y ⥤ C) (TC : C ⥤ C ⥤ C) (TY : Y ⥤ Y ⥤ Y)
    (pi : R ⋙ TY ⟶ (Functor.postcompose₂.obj R).obj
      ((((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj P).obj TC))
    {M N : C} (v : M ⟶ N) (L : Y) :
    (TY.map (R.map v)).app L ≫
      (pi.app N).app L = (pi.app M).app L ≫
      R.map ((Functor.uncurry.obj TC).map (Prod.mkHom v (𝟙 (P.obj L)))) := by
  simp only [Functor.uncurry_obj_map]
  erw [(TC.obj N).map_id]
  simp only [Category.comp_id]
  exact NatTrans.congr_app (pi.naturality v) L

/-- First-variable naturality in the uncurried tensor presentation.
Source: naturality of the specified system projection map
(blueprint: def-sf-refinement-projection-words). -/
theorem tensorNaturality {C Y : Type*} [Category C] [Category Y]
    (R : C ⥤ Y) (P : Y ⥤ C) (TC : C × C ⥤ C) (TY : Y × Y ⥤ Y)
    (pi : R ⋙ Functor.curryObj TY ⟶ (Functor.postcompose₂.obj R).obj
      ((((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj P).obj (Functor.curryObj TC)))
    {M N : C} (v : M ⟶ N) (L : Y) :
    TY.map (Prod.mkHom (R.map v) (𝟙 L)) ≫ (pi.app N).app L =
      (pi.app M).app L ≫ R.map (TC.map (Prod.mkHom v (𝟙 (P.obj L)))) :=
  NatTrans.congr_app (pi.naturality v) L

/-- The purely categorical pasting identity used after normalizing the inner mate and
outer projection. Source: Stacks 0B56, 0DV0
(blueprint: def-sf-refinement-projection-words). -/
theorem projectionPasting
    {X B C Y : Type*} [Category X] [Category B] [Category C] [Category Y]
    (J : X ⥤ B) (J' : X ⥤ C) (S : B ⥤ C) (R : C ⥤ Y) (R' : B ⥤ Y)
    (T : X → Y → X) (TB : B × B ⥤ B) (TC : C × C ⥤ C) (TY : Y × Y ⥤ Y)
    (first : ∀ {M N : Y}, (M ⟶ N) → ∀ L : Y, TY.obj (M, L) ⟶ TY.obj (N, L))
    (first_comp : ∀ {M N O : Y} (v : M ⟶ N) (w : N ⟶ O) L,
      first (v ≫ w) L = first v L ≫ first w L)
    (P : Y ⥤ B) (P' : Y ⥤ C)
    (g : J' ⟶ J ⋙ S) (c : S ⋙ R ⟶ R')
    (d : ∀ K L, TB.obj (J.obj K, P.obj L) ⟶ J.obj (T K L))
    (d' : ∀ K L, TC.obj (J'.obj K, P'.obj L) ⟶ J'.obj (T K L))
    (q : ∀ M L, TC.obj (S.obj M, P'.obj L) ⟶ S.obj (TB.obj (M, P.obj L)))
    (p : ∀ M L, TY.obj (R.obj M, L) ⟶ R.obj (TC.obj (M, P'.obj L)))
    (p' : ∀ M L, TY.obj (R'.obj M, L) ⟶ R'.obj (TB.obj (M, P.obj L)))
    (hn : ∀ {M N : C} (v : M ⟶ N) L,
      first (R.map v) L ≫ p N L =
        p M L ≫ R.map (TC.map (Prod.mkHom v (𝟙 (P'.obj L)))))
    (hd : ∀ K L, d' K L ≫ g.app (T K L) =
      TC.map (Prod.mkHom (g.app K) (𝟙 (P'.obj L))) ≫ q (J.obj K) L ≫ S.map (d K L))
    (hp : ∀ M L, p (S.obj M) L ≫ R.map (q M L) ≫ c.app (TB.obj (M, P.obj L)) =
      first (c.app M) L ≫ p' M L)
    (K : X) (L : Y) :
    (p (J'.obj K) L ≫ R.map (d' K L)) ≫
        (R.map (g.app (T K L)) ≫ c.app (J.obj (T K L))) =
      first (R.map (g.app K) ≫ c.app (J.obj K)) L ≫
        (p' (J.obj K) L ≫ R'.map (d K L)) := by
  simp only [Category.assoc]
  rw [← R.map_comp_assoc, hd]
  simp only [R.map_comp, Category.assoc]
  rw [← reassoc_of% (hn (g.app K) L)]
  have hc := c.naturality (d K L)
  dsimp only [Functor.comp_map] at hc
  rw [hc]
  rw [reassoc_of% (hp (J.obj K) L)]
  rw [first_comp]
  simp only [Category.assoc]

/-- The explicit factors of the projection/refinement pasting diagram.
Source: blueprint composition/refinement calculation
(blueprint: def-sf-refinement-projection-words). -/
structure Words (X B C Y : Type*) [Category X] [Category B] [Category C] [Category Y] where
  J : X ⥤ B
  J' : X ⥤ C
  S : B ⥤ C
  R : C ⥤ Y
  R' : B ⥤ Y
  T : X → Y → X
  TB : B × B ⥤ B
  TC : C × C ⥤ C
  TY : Y × Y ⥤ Y
  first : ∀ {M N : Y}, (M ⟶ N) → ∀ L : Y, TY.obj (M, L) ⟶ TY.obj (N, L)
  first_comp : ∀ {M N O : Y} (v : M ⟶ N) (w : N ⟶ O) L,
    first (v ≫ w) L = first v L ≫ first w L
  P : Y ⥤ B
  P' : Y ⥤ C
  gamma : J' ⟶ J ⋙ S
  comp : S ⋙ R ⟶ R'
  delta : ∀ K L, TB.obj (J.obj K, P.obj L) ⟶ J.obj (T K L)
  delta' : ∀ K L, TC.obj (J'.obj K, P'.obj L) ⟶ J'.obj (T K L)
  inner : ∀ M L, TC.obj (S.obj M, P'.obj L) ⟶ S.obj (TB.obj (M, P.obj L))
  outer : ∀ M L, TY.obj (R.obj M, L) ⟶ R.obj (TC.obj (M, P'.obj L))
  outer' : ∀ M L, TY.obj (R'.obj M, L) ⟶ R'.obj (TB.obj (M, P.obj L))
  projection : ∀ K L, TY.obj (R.obj (J'.obj K), L) ⟶ R.obj (J'.obj (T K L)) :=
    fun K L ↦ outer (J'.obj K) L ≫ R.map (delta' K L)
  projection' : ∀ K L, TY.obj (R'.obj (J.obj K), L) ⟶ R'.obj (J.obj (T K L)) :=
    fun K L ↦ outer' (J.obj K) L ≫ R'.map (delta K L)
  projection_eq : ∀ K L, projection K L =
      outer (J'.obj K) L ≫ R.map (delta' K L) := by intros; rfl
  projection'_eq : ∀ K L, projection' K L =
      outer' (J.obj K) L ≫ R'.map (delta K L) := by intros; rfl

namespace Words
variable {X B C Y : Type*} [Category X] [Category B] [Category C] [Category Y]

/-- Compatibility at the open/proper square, with the final pullback transport.
Source: Stacks 0F7B, 0B56 (blueprint: def-sf-refinement-projection-words). -/
def Local (w : Words X B C Y) : Prop :=
  ∀ K L, w.delta' K L ≫ w.gamma.app (w.T K L) =
    w.TC.map (Prod.mkHom (w.gamma.app K) (𝟙 (w.P'.obj L))) ≫
      w.inner (w.J.obj K) L ≫ w.S.map (w.delta K L)

/-- Compatibility at the outer proper compositor.
Source: Stacks 0DV0, 0B56 (blueprint: def-sf-refinement-projection-words). -/
def Composition (w : Words X B C Y) : Prop :=
  ∀ M L, w.outer (w.S.obj M) L ≫ w.R.map (w.inner M L) ≫
    w.comp.app (w.TB.obj (M, w.P.obj L)) =
    w.first (w.comp.app M) L ≫ w.outer' M L
/-- Assemble the local and proper-composition equations using projection naturality.
Source: the explicit categorical calculation above
(blueprint: def-sf-refinement-projection-words). -/
theorem paste (w : Words X B C Y)
    (hn : ∀ {M N : C} (v : M ⟶ N) L,
      w.first (w.R.map v) L ≫ w.outer N L =
        w.outer M L ≫ w.R.map (w.TC.map (Prod.mkHom v (𝟙 (w.P'.obj L)))))
    (hd : w.Local) (hp : w.Composition) (K : X) (L : Y) :
    (w.outer (w.J'.obj K) L ≫ w.R.map (w.delta' K L)) ≫
      (w.R.map (w.gamma.app (w.T K L)) ≫
        w.comp.app (w.J.obj (w.T K L))) =
    w.first (w.R.map (w.gamma.app K) ≫ w.comp.app (w.J.obj K)) L ≫
      (w.outer' (w.J.obj K) L ≫ w.R'.map (w.delta K L)) :=
  projectionPasting w.J w.J' w.S w.R w.R' w.T w.TB w.TC w.TY
    w.first (fun v v' L ↦ w.first_comp v v' L) w.P w.P' w.gamma w.comp
    w.delta w.delta' w.inner w.outer w.outer' hn hd hp K L

/-- Pasting expressed using the recorded native projection components.
Source: the component equations and categorical pasting
(blueprint: def-sf-refinement-projection-words). -/
theorem pasteNative (w : Words X B C Y)
    (hn : ∀ {M N : C} (v : M ⟶ N) L,
      w.first (w.R.map v) L ≫ w.outer N L =
        w.outer M L ≫ w.R.map (w.TC.map (Prod.mkHom v (𝟙 (w.P'.obj L)))))
    (hd : w.Local) (hp : w.Composition) (K : X) (L : Y) :
    w.projection K L ≫
      (w.R.map (w.gamma.app (w.T K L)) ≫ w.comp.app (w.J.obj (w.T K L))) =
    w.first (w.R.map (w.gamma.app K) ≫ w.comp.app (w.J.obj K)) L ≫
      w.projection' K L := by
  rw [w.projection_eq, w.projection'_eq]
  exact w.paste hn hd hp K L

end Words

/-- Normalize an identity-side direct image before taking the proper/open mate.
Source: blueprint refinement calculation
(blueprint: def-sf-refinement-projection-words). -/
def identityNormalize {X B C : Type*} [Category X] [Category B] [Category C]
    (J : X ⥤ B) (J' : X ⥤ C) (S : X ⥤ X) (U : B ⥤ C)
    (a : 𝟭 X ⟶ S) (g : S ⋙ J' ⟶ J ⋙ U) : J' ⟶ J ⋙ U where
  app K := J'.map (a.app K) ≫ g.app K
  naturality K L v := by
    have h := ((Functor.leftUnitor J').inv ≫ Functor.whiskerRight a J' ≫ g).naturality v
    simpa only [NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Category.id_comp] using h

/-- Equality transport by the original index, without comparing functor values.
Source: equality elimination (blueprint: def-sf-refinement-projection-words). -/
def indexIso {I C : Type*} [Category C] (P : I → C) {i j : I} (h : i = j) :
    P i ≅ P j := by
  cases h
  exact Iso.refl _

/-- The index transport is the usual canonical equality isomorphism.
Source: equality elimination (blueprint: def-sf-refinement-projection-words). -/
theorem eqToIso_congrArg_indexIso {I C : Type*} [Category C] (P : I → C)
    {i j : I} (h : i = j) : eqToIso (congrArg P h) = indexIso P h := by
  cases h
  rfl

/-- The first-variable curried tensor action preserves composition.
Source: functoriality (blueprint: def-sf-refinement-projection-words). -/
theorem curriedFirstComp {Y : Type*} [Category Y] (T : Y ⥤ Y ⥤ Y)
    {M N O : Y} (v : M ⟶ N) (w : N ⟶ O) (L : Y) :
    (T.map (v ≫ w)).app L = (T.map v).app L ≫ (T.map w).app L := by
  rw [T.map_comp, NatTrans.comp_app]

/-- The first-variable tensor action preserves composition.
Source: functoriality (blueprint: def-sf-refinement-projection-words). -/
theorem tensorFirstComp {Y : Type*} [Category Y] (T : Y × Y ⥤ Y)
    {M N O : Y} (v : M ⟶ N) (w : N ⟶ O) (L : Y) :
    T.map (Prod.mkHom (v ≫ w) (𝟙 L)) =
      T.map (Prod.mkHom v (𝟙 L)) ≫ T.map (Prod.mkHom w (𝟙 L)) := by
  rw [← T.map_comp]
  simp only [CategoryTheory.prod_comp, Category.id_comp]

/-- The finite-coefficient factors, retaining all identity and compactification transports.
Source: blueprint composition/refinement calculation
(blueprint: def-sf-refinement-projection-words). -/
abbrev finiteWords (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c₁ c₂ : Compactification f.hom.left} (r : c₁.Refinement c₂) :
    Words (ProperOpenDerived A X.obj.left) (ProperOpenDerived A c₁.Z)
      (ProperOpenDerived A c₂.Z) (ProperOpenDerived A Y.obj.left) := by
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  let J := ProperOpenShriek A c₁.i
  let J' := ProperOpenShriek A c₂.i
  let S := ProperOpenPush A r.hom
  let R := ProperOpenPush A c₂.g
  let R' := ProperOpenPush A c₁.g
  let TB := Functor.uncurry.obj (ProperOpenTensor A c₁.Z)
  let TC := Functor.uncurry.obj (ProperOpenTensor A c₂.Z)
  let TY := Functor.uncurry.obj (ProperOpenTensor A Y.obj.left)
  exact {
    J := J, J' := J', S := S, R := R, R' := R'
    T := fun K L ↦ ((ProperOpenTensor A X.obj.left).obj K).obj
      ((ProperOpenPull A f.hom.left).obj L)
    TB := TB, TC := TC, TY := TY
    first := fun v L ↦ ((ProperOpenTensor A Y.obj.left).map v).app L
    first_comp := curriedFirstComp (ProperOpenTensor A Y.obj.left)
    P := ProperOpenPull A c₁.g, P' := ProperOpenPull A c₂.g
    gamma := identityNormalize J J' (ProperOpenPush A (𝟙 X.obj.left)) S
      ((ordinary F A).sId X).inv
      (properOpenMate A c₁.i (𝟙 X.obj.left) r.hom c₂.i
        (r.i_hom.trans (Category.id_comp _).symm))
    comp := (conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c₂.g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (r.hom ≫ c₂.g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom c₂.g)).hom ≫
      (indexIso (ProperOpenPush A) r.hom_g).hom
    delta := fun K L ↦ ((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) c₁.i).inv.app K).app ((ProperOpenPull A c₁.g).obj L) ≫ J.map
      (((ProperOpenTensor A X.obj.left).obj K).map
        ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₁).hom.app L))
    delta' := fun K L ↦ ((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) c₂.i).inv.app K).app ((ProperOpenPull A c₂.g).obj L) ≫ J'.map
      (((ProperOpenTensor A X.obj.left).obj K).map
        ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₂).hom.app L))
    inner := fun M L ↦ properOpenProjection A r.hom M
      ((ProperOpenPull A c₂.g).obj L) ≫ S.map
      (((ProperOpenTensor A c₁.Z).obj M).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom c₂.g).inv.app L ≫
          (indexIso (ProperOpenPull A) r.hom_g).hom.app L))
    outer := properOpenProjection A c₂.g
    outer' := properOpenProjection A c₁.g
    projection := fun K L ↦
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c₂).app K).app L
    projection' := fun K L ↦
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c₁).app K).app L
    projection_eq := by
      intro K L
      exact (projectionMapOfCompactification_app_app (ModuleCat.{u + 1} A) c₂ K L).trans
        (congrArg (fun v ↦ properOpenProjection A c₂.g (J'.obj K) L ≫ v)
          ((ProperOpenPush A c₂.g).map_comp _ _).symm)
    projection'_eq := by
      intro K L
      exact (projectionMapOfCompactification_app_app (ModuleCat.{u + 1} A) c₁ K L).trans
        (congrArg (fun v ↦ properOpenProjection A c₁.g (J.obj K) L ≫ v)
          ((ProperOpenPush A c₁.g).map_comp _ _).symm) }

end AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection

namespace WeilConjectures.IntegralSystemRealization.RefinementProjection
open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection

/-- The simultaneous-system factors, before evaluation, with all quotient transitions.
Source: blueprint composition/refinement calculation
(blueprint: def-sf-refinement-projection-words). -/
abbrev systemWords (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : FiniteFieldDatum.{u}) (o : Operations l E) (z : Realizations l E F o)
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c₁ c₂ : Compactification f.hom.left} (r : c₁.Refinement c₂) :
    Words (System l E X.obj.left) (System l E c₁.Z)
      (System l E c₂.Z) (System l E Y.obj.left) := by
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  let J := Operations.shriek l E o c₁.i
  let J' := Operations.shriek l E o c₂.i
  let S := Operations.push l E o r.hom
  let TX := (calculus l E X.obj.left).systemClosed.tensor
  let TB := (calculus l E c₁.Z).systemClosed.tensor
  let TC := (calculus l E c₂.Z).systemClosed.tensor
  let TY := (calculus l E Y.obj.left).systemClosed.tensor
  exact {
    J := J, J' := J', S := S
    R := Operations.push l E o c₂.g, R' := Operations.push l E o c₁.g
    T := fun K L ↦ TX.obj (K, (pull l E f.hom.left).obj L)
    TB := TB, TC := TC, TY := TY
    first := fun v L ↦ TY.map (Prod.mkHom v (𝟙 L))
    first_comp := tensorFirstComp TY
    P := pull l E c₁.g, P' := pull l E c₂.g
    gamma := identityNormalize J J' (Operations.push l E o (𝟙 X.obj.left)) S
      (z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
        ProEtale.SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
          X.obj.left).inv
      (z.properOpen.gamma c₁.i (𝟙 X.obj.left) r.hom c₂.i
        (r.i_hom.trans (Category.id_comp _).symm))
    comp := (z.compositors.pushComp l E r.hom c₂.g).hom ≫
      (eqToIso (congrArg (Operations.push l E o) r.hom_g)).hom
    delta := fun K L ↦ (z.openComparisons.projection c₁.i).hom.app
      (K, (pull l E c₁.g).obj L) ≫ J.map (TX.map (Prod.mkHom (𝟙 K)
        ((z.compositors.pullComp c₁.i c₁.g).inv.app L ≫
          eqToHom (congrArg (fun g ↦ (pull l E g).obj L) c₁.comm.symm))))
    delta' := fun K L ↦ (z.openComparisons.projection c₂.i).hom.app
      (K, (pull l E c₂.g).obj L) ≫ J'.map (TX.map (Prod.mkHom (𝟙 K)
        ((z.compositors.pullComp c₂.i c₂.g).inv.app L ≫
          eqToHom (congrArg (fun g ↦ (pull l E g).obj L) c₂.comm.symm))))
    inner := fun M L ↦ ((properProjection l E o r.hom).app M).app
      ((pull l E c₂.g).obj L) ≫ S.map (TB.map (Prod.mkHom (𝟙 M)
        ((z.compositors.pullComp r.hom c₂.g).inv.app L ≫
          eqToHom (congrArg (fun g ↦ (pull l E g).obj L) r.hom_g))))
    outer := fun M L ↦ ((properProjection l E o c₂.g).app M).app L
    outer' := fun M L ↦ ((properProjection l E o c₁.g).app M).app L
    projection := compactificationProjection l E o z.compositors z.openComparisons c₂
    projection' := compactificationProjection l E o z.compositors z.openComparisons c₁
    projection_eq := by intros; rfl
    projection'_eq := by intros; rfl }

end WeilConjectures.IntegralSystemRealization.RefinementProjection
