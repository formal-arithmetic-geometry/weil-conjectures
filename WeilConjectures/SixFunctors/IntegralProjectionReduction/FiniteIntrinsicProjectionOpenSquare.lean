/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionOpenCoordinates
public import Mathlib.Lean.Meta.CongrTheorems
public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionCoordinates
public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionOpenSquareCore
public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionOpenSquareEndpointEquation

/-! # Open comparison for the specified finite tensor realization

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-open-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection FiniteIntrinsicProjectionCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicDerivedEquivalence

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in

private theorem direct_image_paste
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (R : B ⥤ D) (S : A ⥤ C) (G : C ⥤ D)
    (e : F ⋙ R ≅ S ⋙ G) {I : B} {X Y Z : A}
    (a : I ⟶ F.obj X) (b : X ⟶ Y) (c : Y ⟶ Z)
    {d : I ⟶ F.obj Z} (h : a ≫ F.map b ≫ F.map c = d) :
    R.map a ≫ e.hom.app X ≫ G.map (S.map b) ≫ G.map (S.map c) =
      R.map d ≫ e.hom.app Z := by
  have hn := e.hom.naturality (b ≫ c)
  dsimp only [Functor.comp_map] at hn
  have hp : R.map a ≫ e.hom.app X ≫ G.map (S.map b) ≫ G.map (S.map c) =
      R.map (a ≫ F.map b ≫ F.map c) ≫ e.hom.app Z := by
    simp only [Functor.map_comp, Category.assoc] at hn ⊢
    rw [← hn]
  exact hp.trans (congrArg (fun q ↦ R.map q ≫ e.hom.app Z) h)

-- Cache entries may depend on temporary congruence assumptions. Reuse them only
-- when all their free variables belong to the current local context.

private meta def openSquareInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "congruence recursion limit"
  | fuel + 1 =>
    let (_, g) ← g.intros
    g.withContext do
      let t ← Lean.instantiateMVars (← g.getType)
      let entries ← cache.get
      if let some pf := entries[t]? then
        let pf ← Lean.instantiateMVars pf
        let lctx ← Lean.getLCtx
        if !pf.hasMVar && (Lean.collectFVars {} pf).fvarIds.all lctx.contains then
          g.assign pf
          return
      let (a, b) ← if let some (_, a, b) := t.eq? then pure (a, b)
        else if let some (_, a, _, b) := t.heq? then pure (a, b)
        else throwError "unexpected congruence goal {t}"
      let a := a.consumeMData
      let b := b.consumeMData
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else
        let a ← match a with
          | .letE .. => Lean.Meta.whnf a
          | _ => if a.getAppFn.isConstOf ``CategoryTheory.Functor.obj then
              Lean.Meta.whnf a else pure a
        let b ← match b with
          | .letE .. => Lean.Meta.whnf b
          | _ => if b.getAppFn.isConstOf ``CategoryTheory.Functor.obj then
              Lean.Meta.whnf b else pure b
        if a == b then
          if t.isHEq then g.hrefl else g.refl
        else if ← g.proofIrrelHeq then pure ()
        else if t.isEq then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
            { synthAssignedInstances := false }
          for g in gs do openSquareInstanceCongr cache fuel g
        else if a.getAppFn == b.getAppFn &&
            a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
          let f := a.getAppFn
          let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
          let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
          let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
            (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
          let gs ← g.apply (c.proof.beta #[f]) { synthAssignedInstances := false }
          for g in gs do openSquareInstanceCongr cache fuel g
        else
          if t.isHEq then g.hrefl else g.refl
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      if !pf.hasMVar then cache.modify (·.insert t pf)

/-- The coefficient coordinate square for the open tensor factor, before composing
inverse images. Neither the inverse-image compositor nor the constructible output
comparison occurs.

Source: Stacks 0E8I, 07A4; fix-prop-projection-formula.proof.md, same-map sentence.
(blueprint: lem-sf-finite-intrinsic-projection-open-square).

Proof: apply the local open tensor equation finiteIntrinsicProjectionOpenSquareCore
(blueprint: lem-sf-finite-intrinsic-projection-open-square-core) to U, K.obj, P_g V and
k, with W the fixed g-pullback of the inverse realization of L.obj and b the specified
midpoint g-coordinate. That equation identifies the realized inverse open tensor map with
the fixed open projection, before any proper direct image. Apply the intrinsic proper
direct image Rg_* and postcompose its coefficient comparison; naturality of
sfIntrinsicDerivedDirectImageComparison moves the two fixed maps past it
(direct_image_paste), and functoriality identifies the left side with midpoint followed
by fixedOpenPart and the right side with the explicit endpoint
finiteIntrinsicProjectionOpenSquareEndpoint. The endpoint equation
finiteIntrinsicProjectionOpenSquareEndpointEquation
(blueprint: lem-sf-finite-intrinsic-projection-open-square-endpoint-equation) identifies
that endpoint with Rg_* of inverseOnDomain of the intrinsic inverse open tensor map,
followed by beforeCompositor. Compose the two equalities. No proper projection mate is
used; zero inputs, empty or identity opens and m=0 need no extra hypothesis. -/
theorem finiteIntrinsicProjectionOpenSquare
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    midpoint m f c K L U V k l ≫ fixedOpenPart m f c K L =
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).map
          (SystemProjectionFormula.inverseOnDomain
            (SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
              X.obj.hom (c.g ≫ Y.obj.hom) m U
              ((finiteDerivedPullback C.l E m c.g).obj V))) ≫
        beforeCompositor m f c K L U V k l := by
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let Q := compactSupportProjectionSquare f c
  let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  let RZ := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Q.Z
  let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  let Pg := finiteDerivedPullback C.l E m c.g
  let Jf := (openImmersionLowerShriek B c.i).mapDerivedCategory
  let Pf := (upperStar B c.i).leftDerivedFunctor
  let R := proEtaleConstantDerivedDirectImage c.g A
  let Rf := (lowerStar B c.g).rightDerivedFunctor
  let tx := Functor.uncurry.obj (derivedTensor B X.obj.left)
  let tz := Functor.uncurry.obj (derivedTensor B c.Z)
  let sz := canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Q.Z
  let ej := FiniteIntrinsicRealization.openComparison (C := C) (E := E) m f c
  let er : RZ.functor ⋙ R ≅ Rf ⋙ RY.functor :=
    sfIntrinsicDerivedDirectImageComparison c.g A
  let epg : Pg ≅ RY.inverse ⋙ sfFixedDerivedPullback A c.g ⋙ RZ.functor := by
    change (sfIntrinsicPullback A c.g).mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence Y.obj.left A).inverse.mapDerivedCategory ⋙
        sfFixedDerivedPullback A c.g ⋙
          (sfIntrinsicModuleEquivalence c.Z A).functor.mapDerivedCategory
    exact Functor.mapDerivedCategoryCompIso
        (sfIntrinsicModuleEquivalence Y.obj.left A).inverse
        ((upperStar B c.g) ⋙ (sfIntrinsicModuleEquivalence c.Z A).functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
  let pj : RZ.inverse.obj (J.obj U) ≅ Jf.obj (RX.inverse.obj K.obj) := RZ.inverse.mapIso
    (J.mapIso (k ≪≫ (RX.counitIso.app K.obj).symm) ≪≫ ej.app (RX.inverse.obj K.obj)) ≪≫
      (RZ.unitIso.app _).symm
  let W := (upperStar B c.g).leftDerivedFunctor.obj (RY.inverse.obj L.obj)
  let pp : RZ.inverse.obj (Pg.obj V) ≅ W := RZ.inverse.mapIso (Pg.mapIso l ≪≫ epg.app L.obj ≪≫
    RZ.functor.mapIso ((leftDerivedUpperStarIsoMapDerivedCategory B c.g).symm.app
      (RY.inverse.obj L.obj))) ≪≫ (RZ.unitIso.app _).symm
  let t := tz.map (Prod.mkHom pj.hom pp.hom)
  let q : tz.obj (Jf.obj (RX.inverse.obj K.obj), W) ⟶
      Jf.obj (tx.obj (RX.inverse.obj K.obj, Pf.obj W)) :=
    ((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app
    (RX.inverse.obj K.obj)).app W
  have localSquare := finiteIntrinsicProjectionOpenSquareCore m f c U K.obj (Pg.obj V)
    k W pp.hom
  have result := direct_image_paste RZ.functor R Rf RY.functor er
    (X := tz.obj (RZ.inverse.obj (J.obj U), RZ.inverse.obj (Pg.obj V)))
    (Y := tz.obj (Jf.obj (RX.inverse.obj K.obj), W))
    (Z := Jf.obj (tx.obj (RX.inverse.obj K.obj, Pf.obj W)))
    (sz.hom.app (J.obj U, Pg.obj V)) t q localSquare
  have first : midpoint m f c K L U V k l ≫ fixedOpenPart m f c K L =
      finiteIntrinsicProjectionOpenSquareEndpoint m f c K L U V k l := by
    delta FiniteIntrinsicProjectionCoordinates.midpoint fixedOpenPart
      finiteIntrinsicProjectionOpenSquareEndpoint
    dsimp only
    dsimp (config := { failIfUnchanged := false }) only
      [t, q, pj, pp, ej, epg, er, id] at result
    delta FiniteIntrinsicRealization.openComparison at result ⊢
    dsimp (config := { failIfUnchanged := false }) only [id] at result ⊢
    simp only [Functor.map_comp, Category.assoc] at result ⊢
    run_tac Lean.Elab.Tactic.withMainContext do
      let some r := (← Lean.getLCtx).findFromUserName? `result |
        throwError "missing lifted local open square"
      let g ← Lean.Elab.Tactic.getMainGoal
      let src ← Lean.Meta.inferType r.toExpr
      let tgt ← g.getType
      let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src tgt)
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, r.toExpr])
      let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
      openSquareInstanceCongr cache 100 v.mvarId!
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      let lctx ← Lean.getLCtx
      unless (Lean.collectFVars {} pf).fvarIds.all lctx.contains do
        throwError "coordinate proof contains an out-of-scope local variable"
      Lean.Elab.Tactic.replaceMainGoal []
  exact first.trans
    ((finiteIntrinsicProjectionOpenSquareEndpointEquation m f c K L U V k l).symm)

end WeilConjectures.IntegralProjectionReduction
