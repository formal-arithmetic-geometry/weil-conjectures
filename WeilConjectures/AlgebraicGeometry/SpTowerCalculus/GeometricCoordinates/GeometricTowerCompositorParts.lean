/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerGeometricAssembly
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerGeometricAssembly
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions

/-! # The separate open and proper factors of a tower compositor
Source: Stacks 0F7J, compatible-tower calculation, steps 2--4.
(blueprint: def-sp-geometric-tower-compositor-parts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The word after composing the two open extensions, before composing proper images.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
abbrev afterOpenSystem (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h) :=
  (SpTowerShriek.openD l E b (o.openOp T.cfg.i) ⋙
    SpTowerShriek.push l E b (o.geometry T.p)) ⋙
    SpTowerShriek.push l E b (o.geometry T.cg.g)

/-- Realize the three factors remaining after the open compositor.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
abbrev afterOpen (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h) :=
  (realization l E b X (q.abelian X)).functor ⋙ afterOpenSystem l E b o T ⋙
    (realization l E b Z (q.abelian Z)).inverse

/-- The corresponding three-factor model word.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
abbrev modelAfterOpen
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h) :=
  (VaryingRing.J (graphRings l E) (graphTransitions l E) T.cfg.i ⋙
    VaryingRing.P (graphRings l E) (graphTransitions l E) T.p) ⋙
    VaryingRing.P (graphRings l E) (graphTransitions l E) T.cg.g

/-- Coordinates of the three factors, with the realization counit recorded.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
def afterOpenCoordinates
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h) :
    afterOpen l E b o q T ⋙ (nativeCoordinate l E b o q g Z).functor ≅
      (nativeCoordinate l E b o q g X).functor ⋙ modelAfterOpen l E T := by
  let := (q.abelian X).hasDerived
  let := (q.abelian Z).hasDerived
  let := b.realizationAdditive X
  let := b.realizationAdditive Z
  let eX := realization l E b X (q.abelian X)
  let eZ := realization l E b Z (q.abelian Z)
  exact Functor.isoWhiskerLeft (eX.functor ⋙ afterOpenSystem l E b o T)
      (Functor.isoWhiskerRight eZ.counitIso (g.presentation Z).functor.mapDerivedCategory ≪≫
        Functor.leftUnitor _) ≪≫
    Functor.isoWhiskerLeft eX.functor
      (pasteEvaluations
        (pasteEvaluations (graphSystemOpenCoordinates l E b o g T.cfg.i)
          (graphSystemProperCoordinates l E b o g T.p))
        (graphSystemProperCoordinates l E b o g T.cg.g))

/-- Only the open model compositor, with both proper factors still uncomposed.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
def modelOpenCollapse
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h) :
    modelTowerIntermediate l E T ⟶ modelAfterOpen l E T :=
  Functor.whiskerRight
    (Functor.whiskerRight
      (VaryingRing.namedJComp (graphRings l E) (graphTransitions l E)
        T.cf.i T.q T.cfg.i T.i_q).hom
      (VaryingRing.P (graphRings l E) (graphTransitions l E) T.p))
    (VaryingRing.P (graphRings l E) (graphTransitions l E) T.cg.g)

/-- Only the proper model compositor, with the open factor already composed.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
def modelProperCollapse
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h) :
    modelAfterOpen l E T ⟶
      VaryingRing.J (graphRings l E) (graphTransitions l E) T.cfg.i ⋙
        VaryingRing.P (graphRings l E) (graphTransitions l E) T.cfg.g :=
  Functor.whiskerLeft (VaryingRing.J (graphRings l E) (graphTransitions l E) T.cfg.i)
    (VaryingRing.namedPComp (graphRings l E) (graphTransitions l E)
      T.p T.cg.g T.cfg.g T.p_g).hom

/-- The open collapse alone in native coordinates, determined by full faithfulness.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
def openCollapse (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (K : spDerivedCoefficientTowers l E X (q.abelian X)) :
    (towerIntermediate l E b o q T).obj K ⟶ (afterOpen l E b o q T).obj K :=
  (nativeCoordinate l E b o q g Z).fullyFaithfulFunctor.preimage
    ((towerIntermediateCoordinates l E b o q g T).hom.app K ≫
      (modelOpenCollapse l E T).app ((nativeCoordinate l E b o q g X).functor.obj K) ≫
      (afterOpenCoordinates l E b o q g T).inv.app K)

/-- The proper collapse alone in native coordinates, determined by full faithfulness.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
def properCollapse (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (K : spDerivedCoefficientTowers l E X (q.abelian X)) :
    (afterOpen l E b o q T).obj K ⟶ (F l E b o q T.cfg).obj K :=
  (nativeCoordinate l E b o q g Z).fullyFaithfulFunctor.preimage
    ((afterOpenCoordinates l E b o q g T).hom.app K ≫
      (modelProperCollapse l E T).app ((nativeCoordinate l E b o q g X).functor.obj K) ≫
      (nativeSupportCoordinates l E b o q g T.cfg).inv.app K)

/-- The finite three-factor word in fixed module coordinates.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
abbrev finiteAfterOpen
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (n : ℕ) :=
  (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ⋙
    ((towerJ (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cfg.i ⋙
      towerP (ULift.{u + 1} (SpTowerShriek.R l E n)) T.p) ⋙
      towerP (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cg.g)

/-- Evaluate the open factor and the two remaining proper factors separately.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
def afterOpenEvaluation
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (n : ℕ) :
    afterOpen l E b o q T ⋙ fixedLevel l E b q Z n ≅
      spDerivedCoefficientEvaluation l E X (q.abelian X) n ⋙ finiteAfterOpen l E T n :=
  Functor.isoWhiskerRight
      (realizeEvaluation (realization l E b X (q.abelian X))
        (realization l E b Z (q.abelian Z))
        (levelComparison l E b q X n) (levelComparison l E b q Z n)
        (pasteEvaluations
          (pasteEvaluations (SpTowerShriek.openEvaluation l E b (o.openOp T.cfg.i) n)
            ((o.geometry T.p).pushEvaluation n))
          ((o.geometry T.cg.g).pushEvaluation n))) _ ≪≫
    Functor.isoWhiskerLeft _
      (pasteEvaluations
        (pasteEvaluations (finiteOpenFixedCoordinates l E T.cfg.i n)
          (finiteProperFixedCoordinates l E z T.p n))
        (finiteProperFixedCoordinates l E z T.cg.g n))

/-- Finite open contraction, including the four individual fixed coordinates.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
def finiteOpenCollapse (z : FiniteCoordinates l E)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (n : ℕ) : finiteTowerIntermediate l E T n ≅ finiteAfterOpen l E T n :=
  finiteTowerIntermediateCoordinates l E z T n ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight
          (towerOpenComposition (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cf.i T.q ≪≫
            towerOpenCongr (ULift.{u + 1} (SpTowerShriek.R l E n)) T.i_q) _) _)

/-- Finite proper contraction, with the open factor held fixed.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts). -/
def finiteProperCollapse
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (n : ℕ) : finiteAfterOpen l E T n ≅
      (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) T.cfg :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
    ((finiteDirectImageComposition (ULift.{u + 1} (SpTowerShriek.R l E n))
      T.p T.cg.g).symm ≪≫
      eqToIso (congrArg (towerP (ULift.{u + 1} (SpTowerShriek.R l E n))) T.p_g)))

set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option cleanup.letToHave false
attribute [local irreducible] _root_.DerivedCategory _root_.instCategoryDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  nativeCoordinate nativeSupportCoordinates towerIntermediateCoordinates
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

section FiniteWordInstanceTransport
open Lean Meta Elab Tactic CategoryTheory

private theorem typedCastHEq {α β : Sort u} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private meta def nameCoordinateProjection (e : Expr)
    (components : Bool := false) : MetaM Expr := do
  if e.getAppFn.isConstOf ``ProperOpenCalculus.CompactificationRealization.obj ||
      e.getAppFn.isConstOf ``ProperOpenCalculus.CompactificationRealization.category ||
      e.getAppFn.isConstOf ``ProperOpenCalculus.obj ||
      e.getAppFn.isConstOf ``ProperOpenCalculus.category ||
      e.getAppFn.isConstOf ``spDerivedCoefficientTowers ||
      e.getAppFn.isConstOf ``VaryingRing.Derived then
    return ← withConfig (fun cfg => { cfg with zetaDelta := true }) <|
      withDefault <| whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  if components && fn.isConstOf ``ProperOpenCalculus.CompactificationRealization.H then
    return ← withConfig (fun cfg => { cfg with zetaDelta := true }) <|
      withDefault <| whnf e
  if components && (fn.isConstOf ``CategoryTheory.Category.toCategoryStruct ||
      fn.isConstOf ``CategoryTheory.CategoryStruct.toQuiver) && !args.isEmpty then
    let c := args.back!
    let c := if c.getAppFn.isConstOf ``CategoryTheory.Category.toCategoryStruct then
      c.getAppArgs.back! else c
    if c.getAppFn.isConstOf ``CategoryTheory.Functor.category then
      return ← withDefault <| whnf e
  if components && fn.isConstOf ``InducedCategory.Hom.hom then
    return ← withConfig (fun cfg => { cfg with zetaDelta := true }) <|
      withDefault <| whnf e
  let basicProjections := #[`CategoryTheory.Category.toQuiver,
    `CategoryTheory.Category.toCategoryStruct, `CategoryTheory.CategoryStruct.toQuiver]
  if fn.isConst && basicProjections.contains fn.constName! then return e
  if components && fn.isConstOf ``NatTrans.app && args.size == 8 then
    let value := args[6]!
    if value.getAppFn.isConstOf ``Iso.hom || value.getAppFn.isConstOf ``Iso.inv then
      let va := value.getAppArgs
      if va.size == 5 then
        let iapp ← mkAppM ``Iso.app #[va[4]!, args[7]!]
        return ← mkAppM value.getAppFn.constName! #[iapp]
  let field := if fn.isConstOf ``NatTrans.app && args.size == 8 then
      some (``NatTrans, ``NatTrans.app, 6)
    else if fn.isConstOf ``CategoryTheory.Functor.obj && args.size == 6 then
      some (``CategoryTheory.Functor, ``CategoryTheory.Functor.obj, 4)
    else if fn.isConstOf ``CategoryTheory.Functor.map && args.size == 8 then
      some (``CategoryTheory.Functor, ``CategoryTheory.Functor.map, 4)
    else if fn.isConstOf ``Iso.hom && args.size == 5 then some (``Iso, ``Iso.hom, 4)
    else if fn.isConstOf ``Iso.inv && args.size == 5 then some (``Iso, ``Iso.inv, 4)
    else none
  if let some (structureName, fieldName, i) := field then
    let value := args[i]!
    let ty ← inferType value
    let ty ← if ty.getAppFn.isConstOf structureName then pure ty else
      withReducible <| whnf ty
    if ty.getAppFn.isConstOf structureName then
      let p := mkAppN (.const fieldName ty.getAppFn.constLevels!)
        (ty.getAppArgs.push value)
      return mkAppN p (args.extract (i + 1) args.size)
  if e.getAppFn.isConstOf ``ReflQuiver.toQuiver ||
      e.getAppFn.isConstOf ``Subtype.val then
    return ← withConfig (fun cfg => { cfg with zetaDelta := true }) <|
      withDefault <| whnf e
  if e.getAppFn.isConstOf ``Abelian.toPreadditive then
    return ← withConfig (fun cfg => { cfg with zetaDelta := true }) <|
      withDefault <| whnf e
  let .proj n i f := e.getAppFn | return e
  if n == ``CategoryTheory.Category || n == ``CategoryTheory.CategoryStruct ||
      n == ``Quiver then
    let env ← getEnv
    let some info := getStructureInfo? env n | return e
    let some name := getProjFnForField? env n info.fieldNames[i]! | return e
    let ty ← inferType f
    let ty ← if ty.getAppFn.isConstOf n then pure ty else withReducible <| whnf ty
    let p := mkAppN (.const name ty.getAppFn.constLevels!) (ty.getAppArgs.push f)
    return mkAppN p e.getAppArgs
  if n == ``ProperOpenCalculus.CompactificationRealization ||
      (n == ``ProperOpenCalculus && i < 2) then
    return ← withConfig (fun cfg => { cfg with zetaDelta := true }) <|
      withDefault <| whnf e
  if n == ``Abelian || n == ``ReflQuiver || n == ``Subtype then
    return ← withConfig (fun cfg => { cfg with zetaDelta := true }) <|
      withDefault <| whnf e
  let name := if n == ``CategoryTheory.Functor then
      if i == 0 then ``CategoryTheory.Functor.obj else ``CategoryTheory.Functor.map
    else if n == ``Iso then if i == 0 then ``Iso.hom else ``Iso.inv
    else if n == ``NatTrans && i == 0 then ``NatTrans.app
    else if n == ``ObjectProperty.FullSubcategory && i == 0 then
      ``ObjectProperty.FullSubcategory.obj
    else if n == ``InducedCategory.Hom && i == 0 then ``InducedCategory.Hom.hom
    else Name.anonymous
  let env ← getEnv
  let name := if name.isAnonymous then
      match getStructureInfo? env n with
      | some info => (getProjFnForField? env n info.fieldNames[i]!).getD Name.anonymous
      | none => Name.anonymous
    else name
  if name.isAnonymous then return e
  let ty ← inferType f
  let ty ← if ty.getAppFn.isConstOf n then pure ty else whnf ty
  let p := mkAppN (.const name ty.getAppFn.constLevels!) (ty.getAppArgs.push f)
  return mkAppN p e.getAppArgs

private meta def reduceCoordinateObject : Nat → Expr → MetaM Expr
  | 0, e => pure e
  | fuel + 1, e => do
    if e.isFVar then
      if let some val := ((← getLCtx).get! e.fvarId!).value? then
        return ← reduceCoordinateObject fuel val
    if let .letE _ _ val body _ := e then
      return ← reduceCoordinateObject fuel (body.instantiate1 val)
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``CategoryTheory.Functor.obj && args.size == 6 then
      let f := args[4]!
      if f.isFVar then
        if let some val := ((← getLCtx).get! f.fvarId!).value? then
          return ← reduceCoordinateObject fuel (mkAppN fn (args.set! 4 val))
      if let .letE _ _ val body _ := f then
        return ← reduceCoordinateObject fuel
          (mkAppN fn (args.set! 4 (body.instantiate1 val)))
      let h := f.getAppFn
      if h.isConstOf ``fixedLevel || h.isConstOf ``inclusion ||
          h.isConstOf ``restrictedSupport ||
          h.isConstOf ``CategoryTheory.Functor.comp ||
          h.isConstOf ``CategoryTheory.Functor.obj || h.isConstOf ``ObjectProperty.ι ||
          h.isConstOf ``ObjectProperty.lift || h.isConstOf ``CategoryTheory.Functor.id ||
          h.isConstOf ``CategoryTheory.Functor.mapDerivedCategoryPlus ||
          h.isConstOf ``DerivedCategory.Plus.ι ||
          h.isConstOf ``CategoryTheory.Functor.id then
        if let some f' ← withDefault <| unfoldDefinition? f then
          let e' ← whnfCore (mkApp (.proj ``CategoryTheory.Functor 0 f') args[5]!)
          return ← reduceCoordinateObject fuel (← nameCoordinateProjection e')
    if fn.isConstOf ``CategoryTheory.Functor.map && args.size == 8 then
      let f := args[4]!
      let h := f.getAppFn
      if h.isConstOf ``fixedLevel || h.isConstOf ``CategoryTheory.Functor.comp ||
          h.isConstOf ``ObjectProperty.ι || h.isConstOf ``CategoryTheory.Functor.id then
        if let some f' ← withDefault <| unfoldDefinition? f then
          let e' ← whnfCore (mkAppN (.proj ``CategoryTheory.Functor 1 f')
            (args.extract 5 args.size))
          return ← reduceCoordinateObject fuel (← nameCoordinateProjection e')
    if fn.isConstOf ``ObjectProperty.FullSubcategory.obj then
      let arg := args.back!
      let arg' ← reduceCoordinateObject fuel (← nameCoordinateProjection arg)
      if arg' != arg then
        let e' := mkAppN fn (args.set! (args.size - 1) arg')
        if let some e'' ← withDefault <| unfoldDefinition? e' then
          return ← reduceCoordinateObject fuel (← whnfCore e'')
      if let some e' ← Lean.Expr.reduceProjStruct? e then return e'
    return e

private meta def instanceCongr
    (cache : IO.Ref (Std.HashMap (Expr × Expr) (Option Expr)))
    (components norm : Bool) : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "instance congruence depth exhausted"
  | fuel + 1, a, b => do
    let a := (← instantiateMVars a).headBeta.consumeMData
    let b := (← instantiateMVars b).headBeta.consumeMData
    let entries ← cache.get
    if let some h := entries[(a, b)]? then
      if let some h := h then return h
      throwError "cyclic instance transport: {a} versus {b}"
    let h ← (try do
      if a == b then return ← mkHEqRefl a
      if a.getAppFn.isConstOf ``Eq.mpr && a.getAppArgs.size == 4 then
        let aa := a.getAppArgs
        let h ← mkAppM ``typedCastHEq #[aa[2]!, aa[3]!]
        let h' ← instanceCongr cache components norm fuel aa[3]! b
        return ← mkAppM ``HEq.trans #[h, h']
      if b.getAppFn.isConstOf ``Eq.mpr && b.getAppArgs.size == 4 then
        let bb := b.getAppArgs
        let h ← mkAppM ``typedCastHEq #[bb[2]!, bb[3]!]
        let h' ← instanceCongr cache components norm fuel a bb[3]!
        return ← mkAppM ``HEq.trans #[h', ← mkAppM ``HEq.symm #[h]]
      -- These inherited quotient/ULift ring structures are definitionally equal.
      -- Check only ring values here, keeping derived-category constructions folded.
      if (← inferType a).getAppFn.isConstOf ``Ring then
        if ← withDefault <| isDefEq a b then return ← mkHEqRefl a
      if ← isProp (← inferType a) then
        return ← mkAppM ``instanceProofsHEq #[a, b]
      if let .letE _ _ val body _ := a then
        return ← instanceCongr cache components norm fuel (body.instantiate1 val) b
      if let .letE _ _ val body _ := b then
        return ← instanceCongr cache components norm fuel a (body.instantiate1 val)
      if a.isFVar then
        if let some val := ((← getLCtx).get! a.fvarId!).value? then
          return ← instanceCongr cache components norm fuel val b
      if b.isFVar then
        if let some val := ((← getLCtx).get! b.fvarId!).value? then
          return ← instanceCongr cache components norm fuel a val
      if let .lam name ty body info := a then
        if let .lam _ ty' body' _ := b then
          if !body.hasLooseBVars && !body'.hasLooseBVars then
            let a' ← mkAppM ``Function.const #[ty, body]
            let b' ← mkAppM ``Function.const #[ty', body']
            return ← instanceCongr cache components norm fuel a' b'
          if ty != ty' then
            let hd ← instanceCongr cache components norm fuel ty ty'
            let hd ← mkAppM ``eq_of_heq #[hd]
            return ← withLocalDecl name info ty fun x => do
              withLocalDecl (name.appendAfter "'") info ty' fun y => do
                let hxyTy ← mkAppM ``HEq #[x, y]
                withLocalDeclD `hxy hxyTy fun hxy => do
                  let hbody ← instanceCongr cache components norm fuel
                    (body.instantiate1 x) (body'.instantiate1 y)
                  let hbody ← mkLambdaFVars #[x, y, hxy] hbody
                  mkAppM ``Function.hfunext #[hd, hbody]
          return ← withLocalDecl name info ty fun x => do
            let h ← instanceCongr cache components norm fuel
              (body.instantiate1 x) (body'.instantiate1 x)
            let h ← mkAppM ``eq_of_heq #[h]
            let pf ← mkAppM ``funext #[← mkLambdaFVars #[x] h]
            mkAppM ``heq_of_eq #[pf]
      let af := a.getAppFn
      let bf := b.getAppFn
      if af.isMData then
        return ← instanceCongr cache components norm fuel (mkAppN af.consumeMData a.getAppArgs) b
      if bf.isMData then
        return ← instanceCongr cache components norm fuel a (mkAppN bf.consumeMData b.getAppArgs)
      if norm then
        let a' ← nameCoordinateProjection a components
        let b' ← nameCoordinateProjection b components
        if a' != a || b' != b then return ← instanceCongr cache components norm fuel a' b'
        let rec receiverValue (fuel : Nat) (e : Expr) : MetaM Expr := do
          match fuel with
          | 0 => return e
          | fuel + 1 =>
            if e.isFVar then
              if let some v := ((← getLCtx).get! e.fvarId!).value? then
                return ← receiverValue fuel v
            if let .letE _ _ v body _ := e then
              return ← receiverValue fuel (body.instantiate1 v)
            return e
        let sameReceiver ← (if components && af == bf &&
            (af.isConstOf ``CategoryTheory.Functor.obj ||
              af.isConstOf ``CategoryTheory.Functor.map) then do
          let aa := a.getAppArgs
          let bb := b.getAppArgs
          let ra ← receiverValue 20 aa[4]!
          let rb ← receiverValue 20 bb[4]!
          pure (ra == rb)
        else pure false : MetaM Bool)
        if !sameReceiver then
          let a' ← reduceCoordinateObject 30 a
          let b' ← reduceCoordinateObject 30 b
          if a' != a || b' != b then
            return ← instanceCongr cache components norm fuel a' b'
      if af != bf then
        for d in (← getLCtx) do
          let dt ← instantiateMVars d.type
          let dt ← if components then pure dt.consumeMData else withReducible <| whnf dt
          let ht := dt.getAppArgs
          unless dt.getAppFn.isConstOf ``HEq && ht.size == 4 do continue
          let normalizeRingProjection (e : Expr) : MetaM Expr := do
            if let .proj n _ _ := e.getAppFn then
              if n == ``CommRing then return ← nameCoordinateProjection e
            return e
          let ha ← normalizeRingProjection ht[1]!
          let hb ← normalizeRingProjection ht[3]!
          let (a', b', h) ←
            if ha.getAppFn == af && hb.getAppFn == bf then
              pure (ha, hb, d.toExpr)
            else if hb.getAppFn == af && ha.getAppFn == bf then
              pure (hb, ha, ← mkAppM ``HEq.symm #[d.toExpr])
            else continue
          let branchCache ← IO.mkRef (← cache.get)
          let pf? ← observing? do
            let h₁ ← instanceCongr branchCache components norm fuel a a'
            let h₂ ← instanceCongr branchCache components norm fuel b' b
            mkAppM ``HEq.trans #[h₁, ← mkAppM ``HEq.trans #[h, h₂]]
          if let some pf := pf? then
            cache.set (← branchCache.get)
            return pf
      if af == bf && a.getAppArgs.size == b.getAppArgs.size then
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let ct ← mkHCongrWithArity af aa.size
        let cp ← mkAuxTheorem ct.type ct.proof (zetaDelta := !components)
        let mut ps := #[]
        for i in [:aa.size] do
          let mut h ← try instanceCongr cache components norm fuel aa[i]! bb[i]!
            catch ex =>
              if af.isConstOf ``Quiver.Hom && i == 2 then
                throwError "{ex.toMessageData}\nIn {af}, argument {i}\n{aa[i]!}\nversus {bb[i]!}"
              throwError "{ex.toMessageData}\nIn {af}, argument {i}"
          if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
          ps := ps ++ #[aa[i]!, bb[i]!, h]
        let pf := mkAppN cp ps
        if (← inferType pf).isHEq then return pf
        return ← mkAppM ``heq_of_eq #[pf]
      if af != bf then
        let unfolds := #[``ProjectionRestriction.derived, ``SemilinearSections.hasDerived,
          ``SemilinearSections.moduleAbelian, ``inferInstance,
          ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory,
          ``AlgebraicGeometry.Scheme.reductionModules,
          ``AlgebraicGeometry.Scheme.reductionModuleRing,
          ``ProjectionRestriction.Mod, ``ProjectionRestriction.Der,
          ``SemilinearSections.Mod, ``SemilinearSections.D, ``SemilinearSections.DS,
          ``SemilinearSections.Systems, ``SemilinearSections.ring, ``ringedSiteModules,
          ``SheafOfModules.instPreadditive, ``VaryingRing.Modules, ``Compactification.Z,
          ``ProperOpenCalculus.H, ``F, ``compactSupport, ``fixedLevel,
          ``native, ``nativeFor,
          ``CategoryTheory.Functor.comp,
          ``nativeTowerMate, ``nativeTowerCompositors,
          ``openCollapse, ``properCollapse, ``afterOpen, ``afterOpenSystem,
          ``modelOpenCollapse, ``modelProperCollapse,
          ``finiteOpenCollapse, ``finiteProperCollapse, ``finiteTowerContraction,
          ``finiteAfterOpen, ``finiteTowerIntermediate,
          ``finiteTowerIntermediateIntrinsic, ``finiteTowerIntermediateFixed,
          ``rightDerivedLowerShriekOfCompactification, ``towerJ, ``towerP,
          ``ProperOpenCalculus.CompactificationRealization.coordinate,
          ``ProperOpenCalculus.CompactificationRealization.comparison,
          ``ProperOpenCalculus.CompactificationRealization.H,
          ``NativeCoordinates.coordinate, ``NativeCoordinates.comparison]
        if af.isConst && unfolds.contains af.constName! then
          if let some a' ← withDefault <| unfoldDefinition? a then
            return ← instanceCongr cache components norm fuel a' b
        if bf.isConst && unfolds.contains bf.constName! then
          if let some b' ← withDefault <| unfoldDefinition? b then
            return ← instanceCongr cache components norm fuel a b'
      throwError "unmatched instance data: {a} versus {b}"
    catch ex =>
      cache.modify (·.erase (a, b))
      throw ex)
    cache.modify (·.insert (a, b) (some h))
    return h

private meta def expandCoordinateLets (e : Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar id := e | return .continue
    let some value ← id.getValue? | return .continue
    return .visit value
  transform e (pre := pre)

private meta def transportInstances (userName : Name) : TacticM Unit :=
  withMainContext do
    let target ← expandCoordinateLets (← instantiateMVars (← getMainTarget))
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == userName)
      | throwError "no comparison named {userName}"
    let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) (Option Expr))
    let source ← expandCoordinateLets (← instantiateMVars d.type)
    let q ← instanceCongr cache false true 500 target source
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf
-- Retain the binary tower and witnesses as local values during boundary transport.
private meta def transportInstancesLocal (userName : Name) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == userName)
      | throwError "no comparison named {userName}"
    let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) (Option Expr))
    let q ← instanceCongr cache true true 500 target (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf
private meta def closeHEq : TacticM Unit := withMainContext do
  let t ← withReducible <| whnf (← instantiateMVars (← getMainTarget))
  let args := t.getAppArgs
  let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) (Option Expr))
  if t.getAppFn.isConstOf ``HEq then
    let pf ← instanceCongr cache false true 500 args[1]! args[3]!
    (← getMainGoal).assign pf
  else if t.getAppFn.isConstOf ``Eq then
    let h ← instanceCongr cache false true 500 args[1]! args[2]!
    (← getMainGoal).assign (← mkAppM ``eq_of_heq #[h])
  else throwError "expected equality: {t}"

end FiniteWordInstanceTransport

/-- Reconcile proof-irrelevant derived-category instances without expanding
localizations. Source: instance transport in GeometricTowerFactorization. -/
elab "tower_transport " h:ident : tactic => transportInstancesLocal h.getId

private theorem iso_parts_app
    {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : F ≅ H) (hc : a ≪≫ b = c) (M : C) :
    a.hom.app M ≫ b.hom.app M = c.hom.app M := by
  subst c
  rfl

private theorem iso_paste_word
    {C D E₀ : Type*} [Category C] [Category D] [Category E₀]
    (F : C ⥤ D) {U V W : D ⥤ E₀} {H : C ⥤ E₀}
    (a : H ≅ F ⋙ U) (b : U ≅ V) (c : V ≅ W) :
    (a ≪≫ Functor.isoWhiskerLeft F b) ≪≫ Functor.isoWhiskerLeft F c =
      a ≪≫ Functor.isoWhiskerLeft F (b ≪≫ c) := by
  rw [Functor.isoWhiskerLeft_trans, Iso.trans_assoc]

private theorem finite_parts_iso
    (z : FiniteCoordinates l E)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (n : ℕ) : finiteOpenCollapse l E z T n ≪≫ finiteProperCollapse l E T n =
      finiteTowerContraction l E z T n := by
  have result := iso_paste_word
    (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse
    (finiteTowerIntermediateCoordinates l E z T n)
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (towerOpenComposition (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cf.i T.q ≪≫
          towerOpenCongr (ULift.{u + 1} (SpTowerShriek.R l E n)) T.i_q)
        (towerP (ULift.{u + 1} (SpTowerShriek.R l E n)) T.p))
      (towerP (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cg.g))
    (Functor.isoWhiskerLeft
      (towerJ (ULift.{u + 1} (SpTowerShriek.R l E n)) T.cfg.i)
      ((finiteDirectImageComposition (ULift.{u + 1} (SpTowerShriek.R l E n))
          T.p T.cg.g).symm ≪≫
        eqToIso (congrArg (towerP (ULift.{u + 1} (SpTowerShriek.R l E n))) T.p_g)))
  tower_transport result

/-- Paste the finite open and proper collapses, with their recorded equalities.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts).
Proof: expand the three finite words and use preservation of composition under
left whiskering. The intermediate object and its identity associators agree. -/
theorem finite_compositor_parts
    (z : FiniteCoordinates l E)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (n : ℕ) (M : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    (finiteOpenCollapse l E z T n).hom.app M ≫
        (finiteProperCollapse l E T n).hom.app M =
      (finiteTowerContraction l E z T n).hom.app M := by
  have result := iso_parts_app (finiteOpenCollapse l E z T n)
    (finiteProperCollapse l E T n) (finiteTowerContraction l E z T n)
    (finite_parts_iso l E z T n) M
  tower_transport result

private theorem component_factor_eq
    {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (r : F ⟶ H) (m : F ⟶ G) (n : G ⟶ H) (hr : r = m ≫ n) (K : C) :
    r.app K = m.app K ≫ n.app K := by
  subst r
  rfl

private theorem model_compositor_parts
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h) :
    modelTowerCompositors l E T = modelOpenCollapse l E T ≫ modelProperCollapse l E T := by
  rfl

private theorem split_preimage
    {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) (ff : Q.FullyFaithful) {A B C₀ : C} {S T U : D}
    (a : Q.obj A ⟶ S) (d : Q.obj B ≅ T) (c : U ⟶ Q.obj C₀)
    (m : S ⟶ T) (n : T ⟶ U) (r : S ⟶ U) (f : A ⟶ C₀)
    (hr : r = m ≫ n) (hf : Q.map f = a ≫ r ≫ c) :
    f = ff.preimage (a ≫ m ≫ d.inv) ≫
      ff.preimage (d.hom ≫ n ≫ c) := by
  apply ff.map_injective
  simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage,
    Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [hr, Category.assoc] using hf

/-- Factor the two transported compositors at the genuine three-factor word.
Source: Stacks 0F7J (blueprint: def-sp-geometric-tower-compositor-parts).
Proof: apply the faithful target coordinate, use its preimage identities, and
cancel the inverse intermediate coordinate followed by the intermediate coordinate. -/
theorem native_compositor_parts
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} (T : Compactification.Triangle f h)
    (K : spDerivedCoefficientTowers l E X (q.abelian X)) :
    (nativeTowerCompositors l E b o q g T).app K =
      openCollapse l E b o q g T K ≫ properCollapse l E b o q g T K := by
  have hraw := native_tower_compositors_coordinate l E b o q g T K
  simp only [Functor.whiskeringRight_obj_map, Functor.whiskerRight_app] at hraw
  have hc :
      (nativeCoordinate l E b o q g Z).functor.map
          ((nativeTowerCompositors l E b o q g T).app K) =
        (towerIntermediateCoordinates l E b o q g T).hom.app K ≫
          (modelTowerCompositors l E T).app
            ((nativeCoordinate l E b o q g X).functor.obj K) ≫
          (nativeSupportCoordinates l E b o q g T.cfg).inv.app K := by
    unfold nativeTowerCompositors
    run_tac transportInstancesLocal `hraw
  have hs := split_preimage (nativeCoordinate l E b o q g Z).functor
    (nativeCoordinate l E b o q g Z).fullyFaithfulFunctor
    ((towerIntermediateCoordinates l E b o q g T).hom.app K)
    ((afterOpenCoordinates l E b o q g T).app K)
    ((nativeSupportCoordinates l E b o q g T.cfg).inv.app K)
    ((modelOpenCollapse l E T).app ((nativeCoordinate l E b o q g X).functor.obj K))
    ((modelProperCollapse l E T).app ((nativeCoordinate l E b o q g X).functor.obj K))
    ((modelTowerCompositors l E T).app ((nativeCoordinate l E b o q g X).functor.obj K))
    ((nativeTowerCompositors l E b o q g T).app K)
    (component_factor_eq (modelTowerCompositors l E T) (modelOpenCollapse l E T)
      (modelProperCollapse l E T) (model_compositor_parts l E T)
      ((nativeCoordinate l E b o q g X).functor.obj K)) hc
  tower_transport hs

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
