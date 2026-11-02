/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionOpenSquareEndpoint
public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionOpenCoordinates
public import Mathlib.Lean.Meta.CongrTheorems

/-! # Direct-image endpoint of the finite intrinsic projection square

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-open-square-endpoint-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection FiniteIntrinsicProjectionCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor finiteIntrinsicDerivedTensor
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence CompactSupportFiniteProjection.realization
  sixFunctorFiniteRealization integralCoefficientSheaf integralCoefficientCommRingSheaf
  compactSupportProjectionSquare fixedTensor tensor
  Over.homMk CostructuredArrow.homMk
  sixFunctorFiniteSupport sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  derivedTensorRightDerivedLowerStar


set_option maxHeartbeats 800000 in
-- Comparing the specified coefficient realizations needs additional elaboration heartbeats.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in

private theorem endpoint_paste
    {T A B C D : Type*} [Category T] [Category A] [Category B] [Category C] [Category D]
    (tx : T × T ⥤ T) (J : T ⥤ A) (F : A ⥤ B) (R : B ⥤ D)
    (S : A ⥤ C) (G : C ⥤ D) (e : F ⋙ R ≅ S ⋙ G)
    {a₀ a₁ b₀ b₁ b₂ : T} (x : a₀ ⟶ a₁) (y : b₀ ⟶ b₁) (z : b₁ ⟶ b₂)
    {I K H : B} (v : I ⟶ K) (s : K ⟶ H)
    (j : H ⟶ F.obj (J.obj (tx.obj (a₀, b₀)))) :
    R.map v ≫ R.map s ≫ R.map j ≫ e.hom.app _ ≫
        G.map (S.map (J.map (tx.map (Prod.mkHom x (y ≫ z))))) =
      R.map (v ≫ s ≫ j ≫ F.map (J.map (tx.map (Prod.mkHom (𝟙 a₀) y))) ≫
        F.map (J.map (tx.map (Prod.mkHom x z)))) ≫ e.hom.app _ := by
  have ht : tx.map (Prod.mkHom x (y ≫ z)) =
      tx.map (Prod.mkHom (𝟙 a₀) y) ≫ tx.map (Prod.mkHom x z) := by
    rw [← tx.map_comp]
    congr 1
    ext <;> simp
  have hn := e.hom.naturality (J.map (tx.map (Prod.mkHom x (y ≫ z))))
  dsimp only [Functor.comp_map] at hn
  rw [ht] at hn ⊢
  simp only [Functor.map_comp, Category.assoc] at hn ⊢
  rw [← hn]

private theorem endpoint_coordinate_paste
    {A B C X Z Y : Type*} [Category A] [Category B] [Category C]
    [Category X] [Category Z] [Category Y]
    (RX : A ≌ X) (RZ : B ≌ Z) (RY : C ≌ Y)
    (J : X ⥤ Z) (Jf : A ⥤ B) (R : Z ⥤ Y) (Rf : B ⥤ C)
    (Pi : Z ⥤ X) (Pg : Y ⥤ Z) {Pi0 PiF : B ⥤ A} {Pg0 PgF : C ⥤ B}
    {Hi : Z ⥤ X} (ai : Pi ≅ Hi) (bi : Hi ≅ RZ.inverse ⋙ Pi0 ⋙ RX.functor)
    (eg : Pg ≅ RY.inverse ⋙ Pg0 ⋙ RZ.functor) (qi : Pi0 ≅ PiF) (qg : Pg0 ≅ PgF)
    (tx : A × A ⥤ A) (ej : RX.functor ⋙ J ≅ Jf ⋙ RZ.functor)
    (er : RZ.functor ⋙ R ≅ Rf ⋙ RY.functor)
    {U K : X} {V L : Y} (k : U ≅ K) (l : V ≅ L) {H : X} {I : Z}
    (s : H ⟶ RX.functor.obj
      (tx.obj (RX.inverse.obj U, RX.inverse.obj (Pi.obj (Pg.obj V)))))
    (v : I ⟶ J.obj H) :
    let N := Pg.obj V
    let T0 := tx.obj (RX.inverse.obj U, RX.inverse.obj (Pi.obj N))
    let ui := RX.inverse.mapIso ((ai ≪≫ bi).app N ≪≫
      RX.functor.mapIso (qi.app (RZ.inverse.obj N))) ≪≫ (RX.unitIso.app _).symm
    let ug := RZ.inverse.mapIso (eg.app L ≪≫
      RZ.functor.mapIso (qg.app (RY.inverse.obj L))) ≪≫ (RZ.unitIso.app _).symm
    let p := ui ≪≫ PiF.mapIso (RZ.inverse.mapIso (Pg.mapIso l) ≪≫ ug)
    let pp := RZ.inverse.mapIso (Pg.mapIso l ≪≫ eg.app L ≪≫
      RZ.functor.mapIso (qg.app (RY.inverse.obj L))) ≪≫ (RZ.unitIso.app _).symm
    let ei : Pi ⋙ RX.inverse ≅ RZ.inverse ⋙ PiF := Functor.isoWhiskerRight
      (ai ≪≫ bi ≪≫ Functor.isoWhiskerLeft RZ.inverse
        (Functor.isoWhiskerRight qi RX.functor)) RX.inverse ≪≫
      Functor.isoWhiskerLeft (RZ.inverse ⋙ PiF) RX.unitIso.symm
    let ec := (Functor.associator RX.functor J R).symm ≪≫
      Functor.isoWhiskerRight ej R ≪≫ Functor.associator Jf RZ.functor R ≪≫
      Functor.isoWhiskerLeft Jf er ≪≫ (Functor.associator Jf Rf RY.functor).symm
    R.map v ≫ ((J ⋙ R).map s ≫ ec.hom.app T0 ≫
      RY.functor.map ((Jf ⋙ Rf).map
        (tx.map (Prod.mkHom (RX.inverse.map k.hom) p.hom)))) =
    R.map ((v ≫ J.map s ≫ ej.hom.app T0 ≫
      RZ.functor.map (Jf.map (tx.map (Prod.mkHom (𝟙 _) (ei.hom.app N))))) ≫
      RZ.functor.map (Jf.map (tx.map
        (Prod.mkHom (RX.inverse.map k.hom) (PiF.map pp.hom))))) ≫
      er.hom.app (Jf.obj
        (tx.obj (RX.inverse.obj K, PiF.obj (PgF.obj (RY.inverse.obj L))))) := by
  dsimp only
  have h := endpoint_paste tx Jf RZ.functor R Rf RY.functor er
    (RX.inverse.map k.hom)
    ((Functor.isoWhiskerRight
      (ai ≪≫ bi ≪≫ Functor.isoWhiskerLeft RZ.inverse
        (Functor.isoWhiskerRight qi RX.functor)) RX.inverse ≪≫
      Functor.isoWhiskerLeft (RZ.inverse ⋙ PiF) RX.unitIso.symm).hom.app (Pg.obj V))
    (PiF.map ((RZ.inverse.mapIso (Pg.mapIso l ≪≫ eg.app L ≪≫
      RZ.functor.mapIso (qg.app (RY.inverse.obj L))) ≪≫
        (RZ.unitIso.app _).symm).hom)) v (J.map s)
    (ej.hom.app (tx.obj (RX.inverse.obj U, RX.inverse.obj (Pi.obj (Pg.obj V)))))
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id] using h

private meta def endpointProjectionStep : Nat → Expr → MetaM (Option Expr)
  | 0, _ => pure none
  | fuel + 1, e₀ => do
    let e := (← instantiateMVars e₀).consumeMData.headBeta
    if e != e₀ then return some e
    match e with
    | .letE _ _ v body _ => return some (body.instantiate1 v)
    | .fvar id => return (← id.getDecl).value? (allowNondep := true)
    | _ => pure ()
    let args := e.getAppArgs
    let fn := e.getAppFn
    let proj? : Option (Name × Nat × Expr × Option Nat) ← match fn with
      | .proj typeName index major => pure (some (typeName, index, major, none))
      | .const name _ => do
        if let some info ← getProjectionFnInfo? name then
          if args.size > info.numParams then
            let ci ← getConstInfoCtor info.ctorName
            pure (some (ci.induct, info.i, args[info.numParams]!, some info.numParams))
          else pure none
        else pure none
      | _ => pure none
    if let some (typeName, index, major, argIndex) := proj? then
      if let .const ctorName _ := major.getAppFn then
        if let .ctorInfo ci ← getConstInfo ctorName then
          if ci.induct == typeName then
            let value := major.getAppArgs[ci.numParams + index]!
            let tail := match argIndex with
              | none => args
              | some i => args.extract (i + 1) args.size
            return some ((mkAppN value tail).headBeta)
      if let some major' ← endpointProjectionStep fuel major then
        return some (match argIndex with
          | none => mkAppN (.proj typeName index major') args
          | some i => mkAppN fn (args.set! i major'))
      return none
    if let .const name us := fn then
      if #[``SystemProjectionFormula.finitePullComp, ``finiteDerivedPullback,
          ``finiteCoefficientRing, ``realization, ``sixFunctorFiniteRealization,
          ``FiniteIntrinsicProjectionCoordinates.beforeCompositor,
          ``FiniteIntrinsicProjectionCoordinates.fixedCompositorPart,
          ``CompactSupportFiniteProjection.fixedTensor, ``evaluatedTensor,
          ``CompactSupportFiniteProjection.tensor,
          ``sixFunctorFiniteSupport, ``sfIntrinsicCompactSupport, ``sfFixedCompactSupport,
          ``sfAmbientCompactSupportCandidate,
          ``AlgebraicGeometry.ProEtale.leftDerivedUpperStarCompactificationIso,
          ``Functor.comp, ``Functor.uncurry, ``Functor.postcompose₂,
          ``Functor.whiskeringLeft₂, ``Functor.whiskeringLeft, ``Functor.whiskeringRight,
          ``Iso.app, ``Iso.trans, ``Iso.symm, ``Functor.mapIso,
          ``NatTrans.vcomp, ``NatTrans.id, ``NatIso.ofComponents, ``Functor.category,
          ``ObjectProperty.ι, ``inducedFunctor].contains name then
        let ci ← getConstInfo name
        if let .defnInfo _ := ci then
          return some ((← instantiateValueLevelParams ci us).beta args)
    return none

private meta def endpointProjectionNormal (e : Expr) : MetaM Expr :=
  transform e (pre := fun e => do
    let isApp := e.getAppFn.isConstOf ``NatTrans.app ||
      match e.getAppFn with
      | .proj n _ _ => n == ``NatTrans
      | _ => false
    if isApp then
      if let some e' ← endpointProjectionStep 50 e then
        return .visit e'
    return .continue)

-- Cache entries may depend on temporary congruence assumptions. Reuse them only
-- when all their free variables belong to the current local context.

private meta def endpointInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
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
          for g in gs do endpointInstanceCongr cache fuel g
        else if a.getAppFn == b.getAppFn &&
            a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
          let f := a.getAppFn
          let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
          let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
          let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
            (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
          let gs ← g.apply (c.proof.beta #[f]) { synthAssignedInstances := false }
          for g in gs do endpointInstanceCongr cache fuel g
        else
          if t.isHEq then g.hrefl else g.refl
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      if !pf.hasMVar then cache.modify (·.insert t pf)

/-- The direct-image inverse map and `beforeCompositor` reach the common endpoint.
Source: fix-prop-projection-formula.proof.md, same-map sentence; Stacks 0E8I and 07A4.
(blueprint: lem-sf-finite-intrinsic-projection-open-square-endpoint-equation).

Proof: expand beforeCompositor into the intrinsic tensor comparison, compact-support
realization and the pair of unary pullback coordinates. Write compact-support
realization as proper direct image of openComparison followed by the direct-image
comparison. Combine successive inverse realization maps in pullCoordinate by
functoriality. Naturality of the inverse coefficient unit moves the pullback of l
through this expression. The exact-to-left-derived comparison then identifies the
i-coordinate with inversePullback(i). Combining the inverse realization maps on the
g-coordinate gives the specified midpoint coordinate pp, formed from P_g(l), its exact
comparison, the exact-to-left-derived comparison and the coefficient unit. Move the resulting tensor
input map through direct-image comparison by naturality. Combine successive functor
maps and reassociate after precomposing the unchanged inverse open map. The word is
exactly the explicit endpoint. No midpoint or fixed-open projection equation occurs.
Only functoriality and natural isomorphisms are used, so zero inputs, empty and
identity opens, and m = 0 require no extra hypothesis. -/
theorem finiteIntrinsicProjectionOpenSquareEndpointEquation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    (proEtaleConstantDerivedDirectImage c.g
      (Padic.coefficientExtensionRing C.l E (m + 1))).map
        (SystemProjectionFormula.inverseOnDomain
          (SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
            X.obj.hom (c.g ≫ Y.obj.hom) m U
            ((finiteDerivedPullback C.l E m c.g).obj V))) ≫
      beforeCompositor m f c K L U V k l =
    finiteIntrinsicProjectionOpenSquareEndpoint m f c K L U V k l := by
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
  let Pi := finiteDerivedPullback C.l E m c.i
  let N := Pg.obj V
  let sx := canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X
  let ai := Functor.mapDerivedCategoryCompIso
    (sfIntrinsicModuleEquivalence c.Z A).inverse
    ((upperStar B c.i) ⋙ (sfIntrinsicModuleEquivalence X.obj.left A).functor)
  let bi := Functor.isoWhiskerLeft
    (sfIntrinsicModuleEquivalence c.Z A).inverse.mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso (upperStar B c.i)
      (sfIntrinsicModuleEquivalence X.obj.left A).functor)
  let qi := (leftDerivedUpperStarIsoMapDerivedCategory B c.i).symm
  let qg := (leftDerivedUpperStarIsoMapDerivedCategory B c.g).symm
  let v := SystemProjectionFormula.inverseOnDomain
    (SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
      X.obj.hom (c.g ≫ Y.obj.hom) m U N)
  have result := endpoint_coordinate_paste RX RZ RY J Jf R Rf Pi Pg
    ai bi epg qi qg tx ej er k l (sx.hom.app (U, Pi.obj N)) v
  delta beforeCompositor finiteIntrinsicProjectionOpenSquareEndpoint
  dsimp only
  dsimp only [ai, bi, epg, qi, qg, ej, er, id] at result
  delta sfIntrinsicCompactSupportComparison FiniteIntrinsicRealization.openComparison
    FiniteIntrinsicRealization.inversePullback FiniteIntrinsicRealization.pullback
    pullCoordinate at result ⊢
  dsimp (config := { failIfUnchanged := false }) only
    [id, sfAmbientCompactSupportCandidate, sfFixedCompactSupport,
      Functor.comp_map, Functor.comp_obj] at result ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let some r := (← Lean.getLCtx).findFromUserName? `result |
      throwError "missing abstract endpoint identity"
    let g ← Lean.Elab.Tactic.getMainGoal
    let src ← endpointProjectionNormal (← Lean.Meta.inferType r.toExpr)
    let tgt ← endpointProjectionNormal (← g.getType)
    let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src tgt)
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, r.toExpr])
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    endpointInstanceCongr cache 150 v.mvarId!
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures.IntegralProjectionReduction
