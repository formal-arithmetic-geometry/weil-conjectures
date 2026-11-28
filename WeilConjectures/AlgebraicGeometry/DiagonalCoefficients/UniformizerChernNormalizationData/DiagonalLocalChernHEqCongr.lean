/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj

/-! # Heterogeneous congruence for derived arrows

The same derived categories occur in these proofs with syntactically different instance terms
(different abelian structures on module sheaves, different abstracted proofs of their
sheafification), and composites are spelled through definitions such as
`finiteUnitComparison`. Checking such equalities by `rfl` makes the kernel reduce derived
categories as localizations, which is very costly.

The tactic `heq_congr` proves an equation `a = b` (or `HEq a b`) by heterogeneous congruence:
it decomposes both sides along equal heads, unfolds non-derived definitions and reduces
structure projections when needed, uses local `HEq`/`Eq` hypotheses, and leaves to the kernel
only comparisons of instances, propositions and small terms.

We also record generic lemmas putting exact images of Ext classes and the finite comparison
isomorphisms into explicit composites, for use with `heq_congr`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

section HEqCongr
open Lean Meta Elab Tactic

/-- The search monad of `heq_congr`: a cache of proved pairs and the hypotheses in use. -/
meta abbrev HEqM := StateRefT (Std.HashMap (Expr × Expr) Expr × List Expr) MetaM

/-- Namespaces of the derived-category machinery that the congruence search never unfolds. -/
meta def heqRigidPrefixes : List Name :=
  [`DerivedCategory, `HomotopyCategory, `CategoryTheory.DerivedCategory,
    `CategoryTheory.HomotopyCategory, `HomologicalComplex, `CochainComplex,
    `CategoryTheory.Localization, `CategoryTheory.MorphismProperty,
    `HomologicalComplexUpToQuasiIso, `CategoryTheory.Functor.mapDerivedCategory,
    `CategoryTheory.Functor.mapDerivedCategorySingleFunctor,
    `CategoryTheory.Functor.commShiftIso, `CategoryTheory.shiftFunctor,
    `CategoryTheory.Functor.mapHomologicalComplex, `CategoryTheory.Functor.mapHomotopyCategory,
    `CategoryTheory.SingleFunctors, `CategoryTheory.Abelian.Ext.homEquiv]

/-- Projection data `(number of parameters, field index)` of a projection function, or of a
definition whose body is a structure projection of its last argument (such as `Functor.obj`). -/
meta def heqProjInfo? (n : Name) : MetaM (Option (Nat × Nat)) := do
  if let some p ← getProjectionFnInfo? n then return some (p.numParams, p.i)
  let some (.defnInfo d) := (← getEnv).find? n | return none
  lambdaTelescope d.value fun xs body => do
    let .proj _ i (.fvar x) := body | return none
    unless xs.size > 0 && xs.back! == .fvar x do return none
    return some (xs.size - 1, i)

/-- Whether the congruence search may unfold the definition `n`. -/
meta def heqUnfoldable (n : Name) : MetaM Bool := do
  if (← heqProjInfo? n).isSome then return false
  if (← isInstance n) then return false
  if heqRigidPrefixes.any (·.isPrefixOf n) then return false
  match (← getEnv).find? n with
  | some (.defnInfo _) => return true
  | _ => return false

/-- Definitional height of `n`, abbreviations being highest. -/
meta def heqConstHeight (n : Name) : MetaM Nat := do
  match (← getEnv).find? n with
  | some (.defnInfo d) =>
    match d.hints with
    | .regular h => return h.toNat + 1
    | .abbrev => return 1000000
    | _ => return 0
  | _ => return 0

/-- The head constant of the innermost structure of a projection application, or the head
constant of a non-projection application. -/
meta partial def heqKey (e : Expr) : MetaM (Option Name) := do
  let .const n _ := e.getAppFn | return none
  match ← heqProjInfo? n with
  | some (np, _) =>
    let args := e.getAppArgs
    if args.size ≤ np then return none
    heqKey args[np]!
  | none => return some n

/-- Unfold the head constant of `e` once, with beta reduction. -/
meta def heqUnfoldHead? (e : Expr) : MetaM (Option Expr) := do
  let .const n ls := e.getAppFn | return none
  unless (← heqUnfoldable n) do return none
  match (← getEnv).find? n with
  | some (.defnInfo d) =>
    return some ((d.value.instantiateLevelParams d.levelParams ls).betaRev e.getAppRevArgs)
  | _ => return none

/-- Reduce a projection application whose structure (after reducing nested projections) is a
constructor application. -/
meta partial def heqReduceProj? (e : Expr) : MetaM (Option Expr) := do
  let .const n _ := e.getAppFn | return none
  let some (np, i) ← heqProjInfo? n | return none
  let args := e.getAppArgs
  if args.size ≤ np then return none
  let s := args[np]!
  let s ← whnfCore ((← heqReduceProj? s).getD s)
  let .const c _ := s.getAppFn | return none
  let some (.ctorInfo ci) := (← getEnv).find? c | return none
  let some field := s.getAppArgs[ci.numParams + i]? | return none
  return some (mkAppN field (args.extract (np + 1) args.size)).headBeta

/-- One unfolding step on `e`: delta of the head definition, or of the innermost structure of a
projection, followed by projection reduction. -/
meta partial def heqUnfold? (e : Expr) : MetaM (Option Expr) := do
  let .const n _ := e.getAppFn | return none
  match ← heqProjInfo? n with
  | some (np, _) =>
    let args := e.getAppArgs
    if args.size ≤ np then return none
    if let some r ← heqReduceProj? e then return some r
    let s := args[np]!
    let s' ← match ← heqUnfoldHead? s with
      | some s' => pure (some s')
      | none => heqUnfold? s
    match s' with
    | some s' =>
      let e' := mkAppN e.getAppFn (args.set! np s')
      return some ((← heqReduceProj? e').getD e')
    | none => return none
  | none => heqUnfoldHead? e

/-- Unfolding priority of `e` (0 if it cannot be unfolded). -/
meta def heqPriority (e : Expr) : MetaM Nat := do
  if (← heqReduceProj? e).isSome then return 2000000
  let some k ← heqKey e | return 0
  unless (← heqUnfoldable k) do return 0
  heqConstHeight k

/-- A local hypothesis proving `HEq a b` (from `HEq` or `Eq` hypotheses, in either orientation). -/
meta def heqHyp? (a b : Expr) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if let some (_, x, _, y) := t.heq? then
      if x == a && y == b then return some d.toExpr
      if x == b && y == a then return some (← mkHEqSymm d.toExpr)
    else if let some (_, x, y) := t.eq? then
      if x == a && y == b then return some (← mkHEqOfEq d.toExpr)
      if x == b && y == a then return some (← mkHEqOfEq (← mkEqSymm d.toExpr))
  return none

/-- Two applications with the same head and the same number of arguments. -/
meta def heqClose (x a : Expr) : Bool :=
  x == a || (x.getAppFn == a.getAppFn && x.getAppNumArgs == a.getAppNumArgs)

/-- Local hypotheses `HEq l r` (from `HEq` or `Eq` hypotheses, in either orientation) whose
side `l` has the same head as `a`; returns `(l, r, proof of HEq l r)`. -/
meta def heqHypsFrom (a : Expr) : MetaM (Array (Expr × Expr × Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if let some (_, x, _, y) := t.heq? then
      let x := x.consumeMData
      let y := y.consumeMData
      if heqClose x a then out := out.push (x, y, d.toExpr, d.toExpr)
      if heqClose y a then out := out.push (y, x, ← mkHEqSymm d.toExpr, d.toExpr)
    else if let some (_, x, y) := t.eq? then
      let x := x.consumeMData
      let y := y.consumeMData
      if heqClose x a then out := out.push (x, y, ← mkHEqOfEq d.toExpr, d.toExpr)
      if heqClose y a then out := out.push (y, x, ← mkHEqOfEq (← mkEqSymm d.toExpr), d.toExpr)
  return out

/-- Prove `HEq a b` by heterogeneous congruence, unfolding heads when needed. -/
meta partial def heqCongrCore (a b : Expr) :
    HEqM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if let some p := (← get).1.get? (a, b) then return p
  let p ← go a b
  modify fun s => (s.1.insert (a, b) p, s.2)
  return p
where
  hint (p a b : Expr) : MetaM Expr := do
    mkExpectedTypeHint p (← mkHEq a b)
  congr? (a b : Expr) : HEqM (Option Expr) := do
    let (.const na la, .const nb lb) := (a.getAppFn, b.getAppFn) | return none
    unless na == nb && a.getAppNumArgs == b.getAppNumArgs && la.length == lb.length do
      return none
    let as := a.getAppArgs
    let bs := b.getAppArgs
    let some thm ← mkHCongrWithArityForConst? na la as.size | return none
    let mut args : Array Expr := #[]
    for x in as, y in bs, k in thm.argKinds do
      args := args.push x |>.push y
      let some p ← (try some <$> heqCongrCore x y catch _ => pure none) | return none
      match k with
      | .eq =>
        if x == y then args := args.push (← mkEqRefl x)
        else args := args.push (← mkEqOfHEq p)
      | _ => args := args.push p
    return some (← hint (mkAppN thm.proof args) a b)
  go (a b : Expr) : HEqM Expr := do
    if let some p ← heqHyp? a b then return p
    for (l, r, p, h) in ← heqHypsFrom a do
      if (← get).2.contains h then continue
      modify fun s => (s.1, h :: s.2)
      let res ← try
          if l == a then pure (some (← mkHEqTrans p (← heqCongrCore r b)))
          else
            match ← congr? a l with
            | some q => pure (some (← mkHEqTrans (← mkHEqTrans q p) (← heqCongrCore r b)))
            | none => pure none
        catch _ => pure none
      modify fun s => (s.1, s.2.tail)
      if let some res := res then return res
    for (l, r, p, h) in ← heqHypsFrom b do
      if (← get).2.contains h then continue
      modify fun s => (s.1, h :: s.2)
      let res ← try
          if l == b then pure (some (← mkHEqTrans (← heqCongrCore a r) (← mkHEqSymm p)))
          else
            match ← congr? l b with
            | some q =>
              let q' ← mkHEqTrans (← mkHEqSymm p) q
              pure (some (← mkHEqTrans (← heqCongrCore a r) q'))
            | none => pure none
        catch _ => pure none
      modify fun s => (s.1, s.2.tail)
      if let some res := res then return res
    let ta ← inferType a
    if (← isClass? ta).isSome then
      return ← hint (← mkHEqRefl a) a b
    let tb ← inferType b
    if (← isProp ta) && (← isProp tb) then
      return mkApp4 (mkConst ``proof_irrel_heq) ta tb a b
    if a.isLambda && b.isLambda then
      let .lam n ty bodyA bi := a | unreachable!
      let .lam _ _ bodyB _ := b | unreachable!
      let p? ← withLocalDecl n bi ty fun x => do
        let ba := bodyA.instantiate1 x
        let bb := bodyB.instantiate1 x
        unless (← withNewMCtxDepth <| withTransparency .all <|
            isDefEq (← inferType ba) (← inferType bb)) do return none
        return some (← mkLambdaFVars #[x] (← mkEqOfHEq (← heqCongrCore ba bb)))
      if let some p := p? then
        let b' := Expr.lam n ty bodyB bi
        return ← hint (← hint (← mkHEqOfEq (← mkFunExt p)) a b') a b
    let ka ← heqKey a
    let kb ← heqKey b
    let pa ← heqPriority a
    let pb ← heqPriority b
    if a.getAppFn == b.getAppFn && (ka == kb || (pa == 0 && pb == 0)) then
      if let some p ← congr? a b then return p
    if pa > 0 && pa >= pb then
      if let some a' ← heqUnfold? a then return ← hint (← heqCongrCore a' b) a b
    if pb > 0 then
      if let some b' ← heqUnfold? b then return ← hint (← heqCongrCore a b') a b
    if pa > 0 then
      if let some a' ← heqUnfold? a then return ← hint (← heqCongrCore a' b) a b
    if let some p ← congr? a b then return p
    let a' ← whnfCore a
    if a' != a then return ← hint (← heqCongrCore a' b) a b
    let b' ← whnfCore b
    if b' != b then return ← hint (← heqCongrCore a b') a b
    unless (← withNewMCtxDepth <| withTransparency .all <| isDefEq a b) do
      throwError "heq_congr: cannot relate{indentExpr a}\nwith{indentExpr b}"
    hint (← mkHEqRefl a) a b

/-- Close a goal `a = b` or `HEq a b` by heterogeneous congruence. -/
elab "heq_congr" : tactic => liftMetaTactic fun g => do
  let t ← whnfR (← instantiateMVars (← g.getType))
  if let some (α, a, b) := t.eq? then
    let (p, _) ← (heqCongrCore a b).run ({}, [])
    g.assign (mkApp4 (mkConst ``eq_of_heq [← getLevel α]) α a b p)
    return []
  else if let some (_, a, _, b) := t.heq? then
    let (p, _) ← (heqCongrCore a b).run ({}, [])
    g.assign p
    return []
  else throwError "heq_congr: goal is not an equation"

end HEqCongr

section Generic
open SpTowerClasses in
/-- The derived arrow of an Ext class precomposed with a unit, pushed through a square of exact
functors, then conjugated by endpoint maps. -/
theorem mk₀CompMk₀_mapExactFunctor_square_hom
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasExt C₁] [HasExt C₂] [HasExt C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (U : C₁ ⥤ C₂) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (G : C₂ ⥤ C₄) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (F : C₁ ⥤ C₃) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C₃ ⥤ C₄) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (τ : U ⋙ G ≅ F ⋙ V) {P Q : C₁} {I : C₂} {I' : C₄} {P' : C₃}
    (gen : I ⟶ U.obj P) (a : I' ⟶ G.obj I) (c : F.obj P ≅ P') {n : ℕ} (x : Ext P Q n) :
    (Ext.mk₀CompMk₀ a (((Ext.mk₀ gen).comp (x.mapExactFunctor U) (zero_add n)).mapExactFunctor G)
      (τ.hom.app Q)).hom =
    (DerivedCategory.singleFunctor C₄ 0).map (a ≫ G.map gen ≫ τ.hom.app P ≫ V.map c.hom) ≫
      mapSingleArrow V n ((DerivedCategory.singleFunctor C₃ 0).map c.inv ≫
        mapSingleArrow F n x.hom) := by
  let := HasExt.standard C₃
  have hsq := CategoryTheory.Abelian.Ext.mapExactFunctor_square U F G V τ n x
  have h : Ext.mk₀CompMk₀ a
      (((Ext.mk₀ gen).comp (x.mapExactFunctor U) (zero_add n)).mapExactFunctor G)
      (τ.hom.app Q) = (Ext.mk₀ (a ≫ G.map gen ≫ τ.hom.app P)).comp
        ((x.mapExactFunctor F).mapExactFunctor V) (zero_add n) := by
    simp only [Ext.mk₀CompMk₀, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc_of_third_deg_zero]
    rw [Iso.app_hom] at hsq
    rw [hsq, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, Iso.app_hom, Category.assoc]
  rw [h, mapSingleArrow_precompose, ← Functor.map_comp_assoc]
  simp only [Category.assoc, ← V.map_comp, Iso.hom_inv_id, V.map_id]
  erw [Category.comp_id]
  rw [SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext,
    SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp]
  rfl

open SpTowerClasses in
/-- A conjugated exact image of a single arrow, written as an explicit composite. -/
theorem map_comp_mapSingleArrow_eq {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {X Y : C} {X' : D} (c : F.obj X ≅ X')
    (n : ℤ) (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).map c.inv ≫ mapSingleArrow F n f =
      ((DerivedCategory.singleFunctor D 0).map c.inv ≫
          (F.mapDerivedCategorySingleFunctor 0).inv.app X) ≫ F.mapDerivedCategory.map f ≫
        ((F.mapDerivedCategory.commShiftIso n).hom.app _ ≫
          ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧') := by
  simp only [mapSingleArrow, Category.assoc]

/-- The inverse of a whiskered single-object comparison followed by an endpoint isomorphism. -/
theorem compIsoApp_isoWhiskerRight_trans_mapIso_inv_heq {C D DC DD : Type*} [Category C]
    [Category D] [Category DC] [Category DD] {S S' : C ⥤ DC} (h : S' = S) (F' : DC ⥤ DD)
    {F : C ⥤ D} {T : D ⥤ DD} (φ : S ⋙ F' ≅ F ⋙ T) {X : C} {X' : D} (c : F.obj X ≅ X') :
    HEq (Functor.compIsoApp (Functor.isoWhiskerRight (eqToIso h) F' ≪≫ φ) X ≪≫ T.mapIso c).inv
      (T.map c.inv ≫ φ.inv.app X) := by
  subst h
  simp [Functor.compIsoApp]

/-- The shifted comparison of a single object with the identity endpoint. -/
theorem p1DecompositionShiftedComparison_hom_heq {C D DC DD : Type*} [Category C] [Category D]
    [Category DC] [Category DD] [HasShift DC ℤ] [HasShift DD ℤ] (F' : DC ⥤ DD) [F'.CommShift ℤ]
    (S : C ⥤ DC) (T : D ⥤ DD) (F : C ⥤ D) (φ : S ⋙ F' ≅ F ⋙ T) (L : C) (M : D)
    (hM : M = F.obj L) (e : F.obj L ≅ M) (he : HEq e (Iso.refl (F.obj L))) (n : ℤ) :
    HEq (Etale.p1DecompositionShiftedComparison F' S T F φ L M e n).hom
      ((F'.commShiftIso n).hom.app (S.obj L) ≫ (φ.hom.app L)⟦n⟧') := by
  subst hM
  obtain rfl := eq_of_heq he
  unfold Etale.p1DecompositionShiftedComparison
  simp

end Generic

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
