/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import Mathlib.Lean.Meta.CongrTheorems
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteProperProjectionWord
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteOpenProjectionTail

/-! Compatibility of the normalized finite tensor with the projection word. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private theorem properProjection_naturality
    {C D : Type*} [Category C] [Category D]
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (phi : TD ⋙ F ⟶ (F.prod F) ⋙ TC)
    {K K' : C} (a : K ⟶ K') (L : D) :
    TD.map (Prod.mkHom (G.map a) (𝟙 L)) ≫
      adj.homEquiv _ _ (phi.app (G.obj K', L) ≫
        TC.map (Prod.mkHom (adj.counit.app K') (𝟙 _))) =
    adj.homEquiv _ _ (phi.app (G.obj K, L) ≫
        TC.map (Prod.mkHom (adj.counit.app K) (𝟙 _))) ≫
      G.map (TC.map (Prod.mkHom a (𝟙 _))) := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  apply congrArg (adj.homEquiv (TD.obj (G.obj K, L)) (TC.obj (K', F.obj L)))
  have hn := phi.naturality (Prod.mkHom (G.map a) (𝟙 L))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← TC.map_comp, prod_comp, Category.comp_id]
  have hc := adj.counit.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc, F.map_id]

private theorem projectionWord_paste_at
    {V W Vb Wb : Type*}
    [Category V] [Category W] [Category Vb] [Category Wb]
    (ey : W ⥤ Wb) (ez : V ⥤ Vb) (G : V ⥤ W) (Gb : Vb ⥤ Wb)
    (r : G ⋙ ey ≅ ez ⋙ Gb)
    (T : Wb × Wb ⥤ Wb) (S : Vb × Vb ⥤ Vb)
    {A B C : V} {D : W} (p : D ⟶ G.obj A) (q1 : A ⟶ B) (q2 : B ⟶ C)
    {M M' L L' U0 U1 : Vb}
    (j0 : M ⟶ M') (cp : L ⟶ L')
    (tz : ez.obj A ⟶ S.obj (M, L))
    (j : ez.obj C ⟶ U0) (tx : U0 ⟶ U1) (qb : S.obj (M', L') ⟶ U1)
    {Y N : Wb} (ty : ey.obj D ⟶ T.obj (Y, N)) (rk : Y ⟶ Gb.obj M)
    (pb0 : T.obj (Gb.obj M, N) ⟶ Gb.obj (S.obj (M, L')))
    (pb1 : T.obj (Gb.obj M', N) ⟶ Gb.obj (S.obj (M', L')))
    (hp : ey.map p ≫ r.hom.app A ≫
        Gb.map (tz ≫ S.map (Prod.mkHom (𝟙 M) cp)) =
      ty ≫ T.map (Prod.mkHom rk (𝟙 N)) ≫ pb0)
    (hq : ez.map (q1 ≫ q2) ≫ j ≫ tx =
      tz ≫ S.map (Prod.mkHom j0 cp) ≫ qb)
    (hn : T.map (Prod.mkHom (Gb.map j0) (𝟙 N)) ≫ pb1 =
      pb0 ≫ Gb.map (S.map (Prod.mkHom j0 (𝟙 L')))) :
    ey.map (p ≫ G.map q1 ≫ G.map q2) ≫
      (r.hom.app C ≫ Gb.map j) ≫ Gb.map tx =
    ty ≫ T.map (Prod.mkHom (rk ≫ Gb.map j0) (𝟙 N)) ≫
      (pb1 ≫ Gb.map qb) := by
  have hr := r.hom.naturality (q1 ≫ q2)
  dsimp only [Functor.comp_map] at hr
  simp only [Functor.map_comp, Category.assoc] at hr
  have split : S.map (Prod.mkHom j0 cp) =
      S.map (Prod.mkHom (𝟙 M) cp) ≫ S.map (Prod.mkHom j0 (𝟙 L')) := by
    rw [← S.map_comp]
    simp only [prod_comp, Category.comp_id, Category.id_comp]
  calc
    _ = ey.map p ≫ r.hom.app A ≫ Gb.map (ez.map (q1 ≫ q2) ≫ j ≫ tx) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hr]
    _ = ey.map p ≫ r.hom.app A ≫
        Gb.map (tz ≫ S.map (Prod.mkHom j0 cp) ≫ qb) := by rw [hq]
    _ = ty ≫ T.map (Prod.mkHom rk (𝟙 N)) ≫ pb0 ≫
        Gb.map (S.map (Prod.mkHom j0 (𝟙 L')) ≫ qb) := by
      rw [split]
      simpa only [Functor.map_comp, Category.assoc] using congrArg
        (fun z ↦ z ≫ Gb.map (S.map (Prod.mkHom j0 (𝟙 L')) ≫ qb)) hp
    _ = _ := by
      simp only [Functor.map_comp]
      rw [← reassoc_of% hn, ← T.map_comp_assoc]
      simp only [prod_comp, Category.comp_id]

section CoefficientCoordinates

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory HasDerivedCategory.standard derivedTensor
  rightDerivedLowerStarProjectionMap derivedOpenImmersionLowerShriekProjectionIso
  leftDerivedUpperStarCompactificationIso projectionMapOfCompactification

private def nativeProjectionProduct
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (Functor.uncurry.obj (derivedTensor A Y)).obj
      ((rightDerivedLowerShriekOfCompactification A c).obj K, L) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        ((Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L)) := by
  exact ((projectionMapOfCompactification A c).app K).app L

set_option maxHeartbeats 100000 in
-- Normalize the product endpoints before specializing the coefficient ring.
private theorem nativeProjectionProduct_eq
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    nativeProjectionProduct A c K L =
      (((rightDerivedLowerStarProjectionMap A c.g).app
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K)).app L) ≫
      ((lowerStar A c.g).rightDerivedFunctor).map (X :=
      (Functor.uncurry.obj (derivedTensor A c.Z)).obj
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K, ((upperStar
      A c.g).leftDerivedFunctor).obj L)) (Y := ((openImmersionLowerShriek
      A c.i).mapDerivedCategory).obj (((derivedTensor A
      X).obj K).obj (((upperStar A c.i).leftDerivedFunctor).obj (((upperStar
      A c.g).leftDerivedFunctor).obj L))))
      (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
      (((upperStar A c.g).leftDerivedFunctor).obj L)) ≫
        ((lowerStar A c.g).rightDerivedFunctor).map (X :=
      ((openImmersionLowerShriek A c.i).mapDerivedCategory).obj (((derivedTensor
      A X).obj K).obj (((upperStar A
      c.i).leftDerivedFunctor).obj (((upperStar A c.g).leftDerivedFunctor).obj
      L)))) (Y := ((openImmersionLowerShriek A c.i).mapDerivedCategory).obj
      ((Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L))) (((openImmersionLowerShriek
      A c.i).mapDerivedCategory).map (Y :=
      (Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L)) (((derivedTensor A
      X).obj K).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L)))
      := by
  unfold nativeProjectionProduct
  exact projectionMapOfCompactification_app_app A c K L


private theorem nativeProjectionWord_paste
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A))
    {VX VZ VY : Type*} [Category VX] [Category VZ] [Category VY]
    (EX : DerivedCategory (Sheaf (ProEt.topology X) A) ⥤ VX)
    (EZ : DerivedCategory (Sheaf (ProEt.topology c.Z) A) ⥤ VZ)
    (EY : DerivedCategory (Sheaf (ProEt.topology Y) A) ⥤ VY)
    (Jb : VX ⥤ VZ) (Gb : VZ ⥤ VY)
    (r : ((lowerStar A c.g).rightDerivedFunctor) ⋙ EY ≅ EZ ⋙ Gb)
    (j : ((openImmersionLowerShriek A c.i).mapDerivedCategory) ⋙ EZ ≅ EX ⋙ Jb)
    (TY : VY × VY ⥤ VY) (TZ : VZ × VZ ⥤ VZ)
    (ty : EY.obj ((Functor.uncurry.obj (derivedTensor A Y)).obj
      ((rightDerivedLowerShriekOfCompactification A c).obj K, L)) ⟶
      TY.obj (EY.obj ((rightDerivedLowerShriekOfCompactification A c).obj K), EY.obj L))
    {U : VX} {Q : VZ}
    (cp : EZ.obj (((upperStar A c.g).leftDerivedFunctor).obj L) ⟶ Q)
    (tz : EZ.obj ((Functor.uncurry.obj (derivedTensor A c.Z)).obj
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K, ((upperStar
      A c.g).leftDerivedFunctor).obj L)) ⟶ TZ.obj (EZ.obj
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K), EZ.obj
      (((upperStar A c.g).leftDerivedFunctor).obj L)))
    (tx : EX.obj ((Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L)) ⟶ U)
    (qb : TZ.obj (Jb.obj (EX.obj K), Q) ⟶ Jb.obj U)
    (pb0 : TY.obj (Gb.obj (EZ.obj (((openImmersionLowerShriek A
      c.i).mapDerivedCategory).obj K)), EY.obj L) ⟶ Gb.obj (TZ.obj (EZ.obj
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K), Q)))
    (pb1 : TY.obj (Gb.obj (Jb.obj (EX.obj K)), EY.obj L) ⟶ Gb.obj (TZ.obj (Jb.obj (EX.obj K), Q)))
    (hp : EY.map (X := (Functor.uncurry.obj (derivedTensor A Y)).obj
      (((lowerStar A c.g).rightDerivedFunctor).obj (((openImmersionLowerShriek
      A c.i).mapDerivedCategory).obj K), L)) (Y := ((lowerStar A c.g).rightDerivedFunctor).obj
      ((Functor.uncurry.obj (derivedTensor A c.Z)).obj (((openImmersionLowerShriek A
      c.i).mapDerivedCategory).obj K,
      ((upperStar A c.g).leftDerivedFunctor).obj L)))
      (((rightDerivedLowerStarProjectionMap A c.g).app
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K)).app L) ≫
        r.hom.app ((Functor.uncurry.obj (derivedTensor A c.Z)).obj
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K, ((upperStar
      A c.g).leftDerivedFunctor).obj L)) ≫ Gb.map (tz ≫ TZ.map (Prod.mkHom (𝟙
      (EZ.obj (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K)))
      cp)) =
      ty ≫ TY.map
      (Prod.mkHom (r.hom.app (((openImmersionLowerShriek A
      c.i).mapDerivedCategory).obj K)) (𝟙 (EY.obj L))) ≫ pb0)
    (hq : EZ.map (X := (Functor.uncurry.obj (derivedTensor A c.Z)).obj
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K, ((upperStar
      A c.g).leftDerivedFunctor).obj L)) (Y := ((openImmersionLowerShriek
      A c.i).mapDerivedCategory).obj
      ((Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L)))
      ((((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
      (((upperStar A c.g).leftDerivedFunctor).obj L)) ≫
      ((openImmersionLowerShriek A c.i).mapDerivedCategory).map (Y :=
      (Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L)) (((derivedTensor A
      X).obj K).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L)))
      ≫
        j.hom.app ((Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L)) ≫ Jb.map tx =
      tz ≫ TZ.map (Prod.mkHom (j.hom.app K) cp) ≫ qb)
    (hn : TY.map (Prod.mkHom (Gb.map (j.hom.app K)) (𝟙 (EY.obj L))) ≫ pb1 =
      pb0 ≫ Gb.map (TZ.map (Prod.mkHom (j.hom.app K) (𝟙 Q)))) :
    EY.map (nativeProjectionProduct A c K L) ≫
      (Functor.isoWhiskerLeft ((openImmersionLowerShriek A
      c.i).mapDerivedCategory) r ≪≫ Functor.isoWhiskerRight j Gb).hom.app
      ((Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L)) ≫ (Jb ⋙ Gb).map tx =
    ty ≫
      TY.map (Prod.mkHom ((Functor.isoWhiskerLeft ((openImmersionLowerShriek A
      c.i).mapDerivedCategory) r ≪≫ Functor.isoWhiskerRight j Gb).hom.app K) (𝟙 (EY.obj L))) ≫ (pb1
      ≫ Gb.map qb) := by
  have h := projectionWord_paste_at EY EZ ((lowerStar A
      c.g).rightDerivedFunctor) Gb r TY TZ
    (A := (Functor.uncurry.obj (derivedTensor A c.Z)).obj
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K, ((upperStar
      A c.g).leftDerivedFunctor).obj L)) (D :=
      (Functor.uncurry.obj (derivedTensor A Y)).obj (((lowerStar A c.g).rightDerivedFunctor).obj
      (((openImmersionLowerShriek A
      c.i).mapDerivedCategory).obj K), L)) (C := ((openImmersionLowerShriek A
      c.i).mapDerivedCategory).obj ((Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar A
      f).leftDerivedFunctor).obj L)))
    (((rightDerivedLowerStarProjectionMap A c.g).app (((openImmersionLowerShriek
      A c.i).mapDerivedCategory).obj K)).app L)
      (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
      (((upperStar A c.g).leftDerivedFunctor).obj L))
      (((openImmersionLowerShriek A c.i).mapDerivedCategory).map (Y :=
      (Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L)) (((derivedTensor A
      X).obj K).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L)))
      (j.hom.app K) cp tz (j.hom.app ((Functor.uncurry.obj (derivedTensor A X)).obj (K, ((upperStar
      A f).leftDerivedFunctor).obj L))) (Jb.map tx) qb
    (ty)
      (r.hom.app (((openImmersionLowerShriek A c.i).mapDerivedCategory).obj K))
      pb0 pb1 hp hq hn
  simpa only [nativeProjectionProduct_eq, rightDerivedLowerShriekOfCompactification,
    Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, id_eq,
    Functor.map_comp, Category.assoc] using h


end CoefficientCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] comparisonFinitePull comparisonFiniteOpen
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  sfIntrinsicModuleEquivalence derivedTensor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers
  rightDerivedLowerStarProjectionMap derivedOpenImmersionLowerShriekProjectionIso
  leftDerivedUpperStarCompactificationIso projectionMapOfCompactification
  comparisonFiniteF comparisonLevelProjection

-- Canonical class diamonds are equal before substituting the finite quotient ring.
private theorem coefficient_ulift_ring (A : Type u) [CommRing A] :
    (ULift.ring : Ring (ULift.{u + 1, u} A)) = ULift.commRing.toRing := by
  rfl

private theorem coefficient_braided (A : Type u) [CommRing A] :
    (ModuleCat.MonoidalCategory.instBraidedCategory : BraidedCategory (ModuleCat.{u} A)) =
      ModuleCat.MonoidalCategory.symmetricCategory.toBraidedCategory := by
  rfl

-- Adapted from SmoothPurityFiniteLevelFixedProjection and
-- TowerCompactSupportProjectionFormulaIsos: cache ordinary heterogeneous
-- congruence proofs at coefficient-instance argument boundaries.
private meta def projectionHeadAsApplication (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let f := e.getAppFn.consumeMData
  if let .proj n i v := f then
    let env ← Lean.getEnv
    let some info := Lean.getStructureInfo? env n | throwError "unknown structure {n}"
    let some p := Lean.getProjFnForField? env n (info.fieldNames[i]!) |
      throwError "unknown projection {n} {i}"
    let t ← Lean.Meta.whnfD (← Lean.Meta.inferType v)
    let .const _ us := t.getAppFn | throwError "projection has non-structure argument"
    let f := Lean.mkAppN (.const p us) (t.getAppArgs.push v)
    return Lean.mkAppN f e.getAppArgs
  return e

-- Expose composition and tensor wrappers before comparing their dependent arguments.
private meta def projectionNormalizeHead (fuel : Nat) (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e ← projectionHeadAsApplication e.consumeMData
    let names := [``comparisonFiniteProjection, ``finiteF,
      ``SheafOfModules.OpenTensorNormalization.FiniteD,
      ``SheafOfModules.OpenTensorNormalization.FiniteModules,
      ``SheafOfModules.OpenTensorNormalization.finiteTensor,
      ``rightDerivedLowerShriekOfCompactification,
      ``derivedTensorRightDerivedLowerShriek,
      ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
      ``CategoryTheory.Functor.uncurry, ``CategoryTheory.Functor.comp,
      ``CategoryTheory.Functor.postcompose₂, ``CategoryTheory.Functor.whiskeringLeft₂,
      ``CategoryTheory.Functor.whiskeringLeft, ``CategoryTheory.Functor.whiskeringRight,
      ``CategoryTheory.Functor.id, ``id]
    if names.any e.getAppFn.isConstOf then
      if let some e' ← Lean.Meta.unfoldDefinition? e then
        return ← projectionNormalizeHead fuel e'
    let args := e.getAppArgs
    let offset? := if e.getAppFn.isConstOf ``CategoryTheory.Functor.obj && args.size ≥ 2
      then some 2 else if e.getAppFn.isConstOf ``CategoryTheory.Functor.map && args.size ≥ 4
      then some 4 else none
    if let some offset := offset? then
      let i := args.size - offset
      let F' ← projectionNormalizeHead fuel args[i]!
      if F' != args[i]! then
        let e' := Lean.mkAppN e.getAppFn (args.set! i F')
        return ← projectionNormalizeHead fuel
          (← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e'))
    let e' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e)
    let e' ← projectionHeadAsApplication e'
    if e' != e then return ← projectionNormalizeHead fuel e'
    return e

/- Factor coefficient-instance equalities at argument boundaries and cache them.
This is the proof-generating congruence used by FiniteIntrinsicProjectionCoordinates;
every generated equality is checked by Lean's kernel. -/
private meta def coefficientInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "congruence recursion limit"
  | fuel + 1 =>
    let (_, g) ← g.intros
    g.withContext do
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let entries ← cache.get
      if let some pf := entries[t]? then
        let ctx ← Lean.getLCtx
        let missing := pf.find? fun e => match e with
          | .fvar id => !(ctx.contains id)
          | _ => false
        if missing.isNone then
          g.assign pf
          return
      for d in ← Lean.getLCtx do
        if (← Lean.instantiateMVars d.type).consumeMData == t then
          g.assign d.toExpr
          return
      let (a, b) ← if let some (_, a, b) := t.eq? then pure (a, b)
        else if let some (_, a, _, b) := t.heq? then pure (a, b)
        else throwError "unexpected congruence goal {t}"
      let a := a.consumeMData
      let b := b.consumeMData
      for d in ← Lean.getLCtx do
        let dt := (← Lean.instantiateMVars d.type).consumeMData
        if let some (_, x, _, y) := dt.heq? then
          if t.isHEq && x.consumeMData == a && y.consumeMData == b then
            g.assign d.toExpr
            return
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else
        let a ← projectionNormalizeHead 60 a
        let b ← projectionNormalizeHead 60 b
        if a == b then
          if t.isHEq then g.hrefl else g.refl
          return
        if a.isFVar && b.isFVar then
          let t' ← if t.isHEq then Lean.Meta.mkHEq a b else Lean.Meta.mkEq a b
          let g' ← g.change t'
          if t.isHEq then g'.assumption
          else
            try g'.assumption
            catch _ =>
              let gs ← g'.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
                { synthAssignedInstances := false }
              for goal in gs do goal.assumption
          return
        let coherence? := if a.getAppFn.isConstOf ``ULift.ring then
          some ``coefficient_ulift_ring
          else if a.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory then
            some ``coefficient_braided
          else none
        if let some name := coherence? then
          let pf ← Lean.Meta.mkAppOptM name #[some (a.getAppArgs[0]!), none]
          let pf ← if t.isHEq then Lean.Meta.mkAppM ``heq_of_eq #[pf] else pure pf
          let gs ← g.apply pf { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
          let pf ← Lean.instantiateMVars (Lean.mkMVar g)
          cache.modify (·.insert t pf)
          return
        let common := a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0
        let a ← if common then pure a else
          projectionNormalizeHead 60 (← Lean.Meta.whnfD a)
        let b ← if common then pure b else
          projectionNormalizeHead 60 (← Lean.Meta.whnfD b)
        if a == b then
          if t.isHEq then g.hrefl else g.refl
        else if ← g.proofIrrelHeq then pure ()
        else if t.isEq then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.isLambda || b.isLambda then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``Function.hfunext)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.getAppFn == b.getAppFn &&
            a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
          let f := a.getAppFn
          let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
          let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
          let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
            (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
          let mut pf := c.proof.beta #[f]
          for i in [:a.getAppNumArgs] do
            let k := c.argKinds[i + 1]!
            pf := Lean.mkApp pf a.getAppArgs[i]!
            unless k == .fixed do
              pf := Lean.mkApp pf b.getAppArgs[i]!
              if k == .eq || k == .heq then
                let ty ← Lean.Meta.whnfD (← Lean.Meta.inferType pf)
                unless ty.isForall do throwError "missing congruence equality binder"
                let h ← Lean.Meta.mkFreshExprMVar ty.bindingDomain!
                pf := Lean.mkApp pf h
                coefficientInstanceCongr cache fuel h.mvarId!
              else unless k == .subsingletonInst do
                throwError "unsupported congruence argument kind"
          g.assign pf
        else
          throwError "unsupported coefficient congruence at fuel {fuel}:\n{a}\nversus\n{b}"
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)


set_option maxHeartbeats 1500000 in
-- Cached congruence compares dependent functor records and coefficient instances.
/-- The normalized finite tensor comparison identifies the compactification
projection with the prescribed proper/open/compositor word.
Source: blueprint operations proof (2), finite projection normalization.
(blueprint: new-lem-sp-strict-finite-projection-word-compatibility).

Proof: apply strictFiniteProperProjectionWord to the proper factor and
strictFiniteOpenProjectionTail to the open/compositor factor. Expand the native
projection into these two factors. Naturality of the proper coordinate moves it
past the image of the tail. Split the middle tensor coordinate into its second-
variable and first-variable factors. Substitute the open square, then the proper
square. Naturality of the target proper projection transpose moves the open
coordinate to the source tensor. Functoriality combines the two source tensor
coordinates into comparisonFiniteF. Unfold the target word and reassociate.
The private projectionWord_paste_at calculation proves this at arbitrary
objects; properProjection_naturality supplies its only naturality premise.
The native decomposition and complete pasting are proved over an arbitrary
abelian coefficient category with the listed tensor and resolution structures,
before specializing to the given finite-level realization. Generic ring and
braiding reflexivity lemmas, then cached heterogeneous congruence, identify the
coefficient-instance diamonds and the thin functor wrappers. Every generated
equality proof is checked by the kernel; no operation model is replaced.
The same argument applies to zero objects, empty schemes and identity factors.
-/
theorem strictFiniteProjectionWordCompatibility (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (coordinates : StrictFiniteCoordinates l E b)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    (hpin : (∀ (T : Scheme.{u}) (n : ℕ),
    ∃ e : SheafOfModules.OpenTensorNormalization.FiniteRealization.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n),
    ∃ t : AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel.{u} (B l E T n),
    ∃ d : SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
        (ULift.{u + 1, u} (R l E n)) T ⋙ e.derived ≅
          (e.derived.prod e.derived) ⋙ t.functor,
      HEq e.equivalence (sfIntrinsicModuleEquivalence T (R l E n)) ∧
      HEq e.underlying (comparisonFiniteUnderlying l E b T n) ∧
      HEq t.functor (comparisonLevelTensor l E b T n) ∧
      ComparisonFiniteTensorRepresentative l E b T n t ∧ HEq d (tensor T n) ∧
      Nonempty (@SheafOfModules.OpenTensorNormalization.FiniteTensorPin.{u}
        (ULift.{u + 1, u} (R l E n)) _ _ T (B l E T n)
        (comparisonFiniteConstantSection l E T n) e t d))) :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (n : ℕ)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))),
      (comparisonFiniteRealization l E b Y n).map
          (comparisonFiniteProjection l E b c n K L) ≫
        (comparisonFiniteF l E b coordinates c n).hom.app
          ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) X).obj
              (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                f).leftDerivedFunctor.obj L)) ≫
        (finiteF l E b c n).map
          ((tensor X n).hom.app
              (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                f).leftDerivedFunctor.obj L) ≫
            (comparisonLevelTensor l E b X n).map
              (Prod.mkHom (𝟙 _) ((comparisonFinitePull l E b f n).hom.app L))) =
      (tensor Y n).hom.app
          ((rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).obj K, L) ≫
        (comparisonLevelTensor l E b Y n).map
          (Prod.mkHom ((comparisonFiniteF l E b coordinates c n).hom.app K) (𝟙 _)) ≫
      comparisonLevelProjection l E b o levels c n
        ((comparisonFiniteRealization l E b X n).obj K)
        ((comparisonFiniteRealization l E b Y n).obj L) := by
  intro X Y f _ _ _ c n K L
  -- Fix the coefficient instances before specializing the native components.
  let : IsGrothendieckAbelian.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) := inferInstance
  let : MonoidalPreadditive
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) := inferInstance
  let : UpperStarPreservesFlat
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) := inferInstance
  have h := nativeProjectionWord_paste
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
    c
    K
    L
    (comparisonFiniteRealization l E b X n)
    (comparisonFiniteRealization l E b c.Z n)
    (comparisonFiniteRealization l E b Y n)
    (sfIntrinsicDerivedOpen (R l E n) c.i)
    ((proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor)
    (coordinates.val c.g n).right
    (comparisonFiniteOpen l E b c.i n)
    (comparisonLevelTensor l E b Y n)
    (comparisonLevelTensor l E b c.Z n)
    ((tensor Y n).hom.app ((rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).obj K, L))
    ((comparisonFinitePull l E b c.g n).hom.app L)
    ((tensor c.Z n).hom.app (((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E
      n))) c.i).mapDerivedCategory).obj K, ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E
      n))) c.g).leftDerivedFunctor).obj L))
    ((tensor X n).hom.app (K, ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
      f).leftDerivedFunctor).obj L) ≫ (comparisonLevelTensor l E b X n).map (Prod.mkHom (𝟙 _)
      ((comparisonFinitePull l E b f n).hom.app L)))
    ((levels.openTensor c.i n ((comparisonFiniteRealization l E b X n).obj K)
      ((proEtaleConstantRingDerivedPullback (R l E n) c.g).obj ((comparisonFiniteRealization l E b Y
      n).obj L))).hom ≫ (sfIntrinsicDerivedOpen (R l E n) c.i).map ((comparisonLevelTensor l E b X
      n).map (Prod.mkHom (𝟙 ((comparisonFiniteRealization l E b X n).obj K))
      (((proEtaleConstantRingPullbackComposition c.i c.g (R l E n)).hom ≫ eqToHom (congrArg (fun h ↦
      proEtaleConstantRingDerivedPullback (R l E n) h) c.comm.symm)).app
      ((comparisonFiniteRealization l E b Y n).obj L)))))
    ((Adjunction.mapDerivedCategoryRightDerivedAdjunction (proEtaleConstantRingAdjunction (R l E n)
      c.g)).homEquiv ((comparisonLevelTensor l E b Y n).obj (((proEtaleConstantRingPushforward (R l
      E n) c.g).rightDerivedFunctor).obj ((comparisonFiniteRealization l E b c.Z n).obj
      (((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
      c.i).mapDerivedCategory).obj K)), ((comparisonFiniteRealization l E b Y n).obj L)))
      ((comparisonLevelTensor l E b c.Z n).obj (((comparisonFiniteRealization l E b c.Z n).obj
      (((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
      c.i).mapDerivedCategory).obj K)), (proEtaleConstantRingDerivedPullback (R l E n) c.g).obj
      ((comparisonFiniteRealization l E b Y n).obj L))) ((levels.tensorPullback c.g n).hom.app
      (((proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor).obj
      ((comparisonFiniteRealization l E b c.Z n).obj (((openImmersionLowerShriek (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (R l E n))) c.i).mapDerivedCategory).obj K)), ((comparisonFiniteRealization
      l E b Y n).obj L)) ≫ (comparisonLevelTensor l E b c.Z n).map (Prod.mkHom
      ((Adjunction.mapDerivedCategoryRightDerivedAdjunction (proEtaleConstantRingAdjunction (R l E
      n) c.g)).counit.app ((comparisonFiniteRealization l E b c.Z n).obj (((openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c.i).mapDerivedCategory).obj K))) (𝟙 _))))
    ((Adjunction.mapDerivedCategoryRightDerivedAdjunction (proEtaleConstantRingAdjunction (R l E n)
      c.g)).homEquiv ((comparisonLevelTensor l E b Y n).obj (((proEtaleConstantRingPushforward (R l
      E n) c.g).rightDerivedFunctor).obj ((sfIntrinsicDerivedOpen (R l E n) c.i).obj
      ((comparisonFiniteRealization l E b X n).obj K)), ((comparisonFiniteRealization l E b Y n).obj
      L))) ((comparisonLevelTensor l E b c.Z n).obj (((sfIntrinsicDerivedOpen (R l E n) c.i).obj
      ((comparisonFiniteRealization l E b X n).obj K)), (proEtaleConstantRingDerivedPullback (R l E
      n) c.g).obj ((comparisonFiniteRealization l E b Y n).obj L))) ((levels.tensorPullback c.g
      n).hom.app (((proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor).obj
      ((sfIntrinsicDerivedOpen (R l E n) c.i).obj ((comparisonFiniteRealization l E b X n).obj K)),
      ((comparisonFiniteRealization l E b Y n).obj L)) ≫ (comparisonLevelTensor l E b c.Z n).map
      (Prod.mkHom ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (proEtaleConstantRingAdjunction (R l E n) c.g)).counit.app ((sfIntrinsicDerivedOpen (R l E n)
      c.i).obj ((comparisonFiniteRealization l E b X n).obj K))) (𝟙 _))))
    (strictFiniteProperProjectionWord l E b o levels coordinates tensor hpin c.g n
      (((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
      c.i).mapDerivedCategory).obj K) L)
    (strictFiniteOpenProjectionTail l E b o levels tensor hpin c n K L)
    (properProjection_naturality (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (proEtaleConstantRingAdjunction (R l E n) c.g)) (comparisonLevelTensor l E b c.Z n)
      (comparisonLevelTensor l E b Y n) (levels.tensorPullback c.g n).hom ((comparisonFiniteOpen l E
      b c.i n).hom.app K) ((comparisonFiniteRealization l E b Y n).obj L))
  delta comparisonFiniteF comparisonLevelProjection
  dsimp only [finiteF, Functor.comp_obj, Functor.comp_map,
    Functor.id_obj, Functor.id_map, Functor.prod_obj, Functor.prod_map, id_eq] at h ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let some r := (← Lean.getLCtx).findFromUserName? `h |
      throwError "missing projection word calculation"
    let g ← Lean.Elab.Tactic.getMainGoal
    let src ← Lean.instantiateMVars (← Lean.Meta.inferType r.toExpr)
    let tgt ← Lean.instantiateMVars (← g.getType)
    let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src tgt)
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, r.toExpr])
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    Lean.Meta.withTransparency .default do
      coefficientInstanceCongr cache 100 v.mvarId!
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale.SpTowerShriek
