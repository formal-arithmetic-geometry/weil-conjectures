/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1SectionEvaluation
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstScalarTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeProjectionTensorInterface
public import WeilConjectures.AlgebraicGeometry.RationalP1.NormalizedProjectionAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveProjectionNaturalityRight
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1TensorShiftNaturality
public import WeilConjectures.AlgebraicGeometry.RationalP1.SectionEvaluationCongruence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The trace-free first projective-line Kunneth comparison

Source: the First identity in the current rational projective-line triangle proof.
(blueprint: lem-sfb-rational-p1-first-trace-pretrace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientPullbackComparison

private theorem pretraceCast_heq {α β : Sort u} (h : α = β) (a : α) :
    HEq (Eq.mp h a) a := by
  cases h
  rfl

private theorem pretraceSubsingleton_heq {α β : Sort u} [Subsingleton α]
    (h : α = β) (a : α) (b : β) : HEq a b := by
  subst β
  exact heq_of_eq (Subsingleton.elim a b)

private theorem pretraceShrink_heq {α β : Type v} [Small.{w} α] [Small.{w} β]
    (h : α = β) : HEq (Shrink.{w} α) (Shrink.{w} β) := by
  subst β
  rfl

private theorem pretraceQuot_heq {α β : Sort v} (r : α → α → Prop)
    (s : β → β → Prop) (hα : α = β) (hr : HEq r s) : HEq (Quot r) (Quot s) := by
  subst β
  have h : r = s := eq_of_heq hr
  subst s
  rfl

private meta structure PretraceCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

private meta partial def pretraceHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT PretraceCongrState MetaM Expr := do
  -- Assigned universe and instance variables must be resolved before matching heads.
  let lhs := (← instantiateMVars lhs).consumeMData
  let rhs := (← instantiateMVars rhs).consumeMData
  if lhs == rhs then return ← mkHEqRefl lhs
  for (a, b, h) in (← get).proofs do
    if a == lhs && b == rhs then return h
    if a == rhs && b == lhs then return ← mkAppM ``HEq.symm #[h]
  if fuel == 0 then throwError "coefficient congruence exhausted: {lhs}
{rhs}"
  let next := fuel - 1
  let prove : StateRefT PretraceCongrState MetaM Expr := do
    if let .letE _ _ value body _ := lhs.getAppFn then
      return ← pretraceHEq (mkAppN (body.instantiate1 value) lhs.getAppArgs) rhs next
    if let .letE _ _ value body _ := rhs.getAppFn then
      return ← pretraceHEq lhs (mkAppN (body.instantiate1 value) rhs.getAppArgs) next
    if lhs.getAppFn.isLambda && !lhs.getAppArgs.isEmpty then
      return ← pretraceHEq lhs.headBeta rhs next
    if rhs.getAppFn.isLambda && !rhs.getAppArgs.isEmpty then
      return ← pretraceHEq lhs rhs.headBeta next
    if lhs.isAppOf ``Eq.mp && lhs.getAppArgs.size == 4 then
      let xs := lhs.getAppArgs
      let h ← mkAppM ``pretraceCast_heq #[xs[2]!, xs[3]!]
      return ← mkAppM ``HEq.trans #[h, ← pretraceHEq xs[3]! rhs next]
    if rhs.isAppOf ``Eq.mp && rhs.getAppArgs.size == 4 then
      let ys := rhs.getAppArgs
      let h ← mkAppM ``pretraceCast_heq #[ys[2]!, ys[3]!]
      return ← mkAppM ``HEq.trans #[← pretraceHEq lhs ys[3]! next,
        ← mkAppM ``HEq.symm #[h]]
    if lhs.isAppOf ``Quot && rhs.isAppOf ``Quot then
      let xs := lhs.getAppArgs
      let ys := rhs.getAppArgs
      let hα ← mkEqOfHEq (← pretraceHEq xs[0]! ys[0]! next)
      let hr ← pretraceHEq xs[1]! ys[1]! next
      return ← mkAppM ``pretraceQuot_heq #[xs[1]!, ys[1]!, hα, hr]
    if lhs.isAppOf ``Shrink && rhs.isAppOf ``Shrink then
      let xs := lhs.getAppArgs
      let ys := rhs.getAppArgs
      let hα ← mkEqOfHEq (← pretraceHEq xs[0]! ys[0]! next)
      return ← mkAppOptM ``pretraceShrink_heq
        #[some xs[0]!, some ys[0]!, some xs[1]!, some ys[1]!, some hα]
    if (← isProof lhs) && (← isProof rhs) then
      return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
    let α ← inferType lhs
    if α.isAppOf ``Abelian || α.isAppOf ``Preadditive then
      let β ← inferType rhs
      if α.getAppFn == β.getAppFn then
        try
          if α == β then
            return ← mkHEqOfEq (← mkAppM ``Subsingleton.elim #[lhs, rhs])
          let hα ← mkEqOfHEq (← pretraceHEq α β next)
          return ← mkAppM ``pretraceSubsingleton_heq #[hα, lhs, rhs]
        catch _ => pure ()
    let wrapper (e : Expr) : Bool :=
      let names := [``DiagonalCoefficients.Modules,
        ``moduleObjectDerivedPullback, ``moduleObjectDerivedPushforward,
        ``DiagonalCoefficients.derivedUpper, ``DiagonalCoefficients.derivedLower,
        ``tracePull, ``tracePush, ``traceAbstractMate, ``ambientPullbackComparison,
        ``secondPretraceExchangeMap, ``ambientExchangeInverse,
        ``projectionModuleMonoidal, ``projectionModuleAbelian,
        ``projectionModuleHasDerived, ``projectionDerivedMonoidal,
        ``projectionCoefficientMonObj, ``projectionSheafMonoidal, ``projectionModuleCategory,
        ``GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall,
        ``GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall,
        ``GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall,
        ``ProEtale.sheafMonoidalCategory, ``ProEtale.sheafBraidedCategory,
        ``ProEtale.sheafSymmetricCategory]
      names.any e.getAppFn.isConstOf
    if lhs.getAppFn != rhs.getAppFn then
      if wrapper lhs then
        if let some lhs' ← unfoldDefinition? lhs (ignoreTransparency := true) then
          return ← pretraceHEq lhs' rhs next
      if wrapper rhs then
        if let some rhs' ← unfoldDefinition? rhs (ignoreTransparency := true) then
          return ← pretraceHEq lhs rhs' next
    if let .fvar id := lhs then
      if let some value := (← id.getDecl).value? then
        return ← pretraceHEq value rhs next
    if let .fvar id := rhs then
      if let some value := (← id.getDecl).value? then
        return ← pretraceHEq lhs value next
    if lhs.isAppOf ``id then
      return ← pretraceHEq lhs.getAppArgs.back! rhs next
    if rhs.isAppOf ``id then
      return ← pretraceHEq lhs rhs.getAppArgs.back! next
    match lhs, rhs with
    | .lam n α body _, .lam _ β body' _ =>
      let hα ← mkEqOfHEq (← pretraceHEq α β next)
      let init ← get
      let hfun ← withLocalDeclD n α fun x =>
        withLocalDeclD (n.appendAfter "'") β fun y => do
        withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
          modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
          let h ← pretraceHEq (body.instantiate1 x) (body'.instantiate1 y) next
          mkLambdaFVars #[x, y, hxy] h
      let congrs := (← get).congrs
      set { init with congrs := congrs }
      let ty ← whnf (← inferType lhs)
      let ty' ← whnf (← inferType rhs)
      let P := mkLambda n .default α ty.bindingBody!
      let Q := mkLambda n .default β ty'.bindingBody!
      return ← mkAppOptM ``Function.hfunext #[some α, some β, some P, some Q,
        some lhs, some rhs, some hα, some hfun]
    | .forallE n α body _, .forallE _ β body' _ =>
      let hα ← mkEqOfHEq (← pretraceHEq α β next)
      let P := mkLambda n .default α body
      let Q := mkLambda n .default β body'
      let hPQ ← pretraceHEq P Q next
      let h ← mkAppOptM ``sectionEvaluationPiEq #[some α, some β, some P, some Q,
        some hα, some hPQ]
      return ← mkHEqOfEq h
    | _, _ => pure ()
    let expandProjection (e : Expr) : MetaM Expr := do
      let .proj typeName index major := e.getAppFn | return e
      let info := Lean.getStructureInfo (← getEnv) typeName
      let p ← mkProjection major info.fieldNames[index]!
      return mkAppN p e.getAppArgs
    let lhs' ← expandProjection lhs
    let rhs' ← expandProjection rhs
    if lhs' != lhs || rhs' != rhs then
      return ← pretraceHEq lhs' rhs' next
    let compObj (e : Expr) : Bool :=
      let F? : Option Expr := match e.getAppFn with
        | .proj name 0 F => if name == ``CategoryTheory.Functor then some F else none
        | _ => if e.isAppOf ``Functor.obj && e.getAppArgs.size ≥ 2 then
            some e.getAppArgs[e.getAppArgs.size - 2]!
          else none
      match F? with
      | some F => F.isAppOf ``Functor.comp || F.isAppOf ``Functor.id
      | none => false
    match compObj lhs with
    | true =>
      let lhs' ← whnf lhs
      if lhs' != lhs then return ← pretraceHEq lhs' rhs next
    | false => pure ()
    match compObj rhs with
    | true =>
      let rhs' ← whnf rhs
      if rhs' != rhs then return ← pretraceHEq lhs rhs' next
    | false => pure ()
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let xs := lhs.getAppArgs
    let ys := rhs.getAppArgs
    if f == g && xs.size == ys.size && !xs.isEmpty then
      let init ← get
      try
        let mut found := none
        for (ff, arity, thm) in (← get).congrs do
          if ff == f && arity == xs.size then found := some thm
        let thm? ← match found with
          | some thm => pure (some thm)
          | none => do
            let thm? ← if let .const name levels := f then
              mkHCongrWithArityForConst? name levels xs.size
            else
              try pure (some (← mkHCongrWithArity f xs.size))
              catch _ => pure none
            if let some thm := thm? then
              modify fun st => {st with congrs := st.congrs.push (f, xs.size, thm)}
            pure thm?
        if let some thm := thm? then
          let mut args := #[]
          for i in [:xs.size] do
            let h ← pretraceHEq xs[i]! ys[i]! next
            let h ← if thm.argKinds[i]! == .eq then mkEqOfHEq h else pure h
            args := args ++ #[xs[i]!, ys[i]!, h]
          let h := mkAppN thm.proof args
          let ty ← inferType h
          if ty.isHEq then return h else return ← mkHEqOfEq h
        else
          let ty ← whnf (← inferType lhs)
          let ty' ← whnf (← inferType rhs)
          if ty.isForall && ty'.isForall then
            let lhs' := mkLambda ty.bindingName! .default ty.bindingDomain!
              (mkApp (lhs.liftLooseBVars 0 1) (.bvar 0))
            let rhs' := mkLambda ty'.bindingName! .default ty'.bindingDomain!
              (mkApp (rhs.liftLooseBVars 0 1) (.bvar 0))
            return ← pretraceHEq lhs' rhs' next
      -- Some wrappers ignore parameters. If argumentwise congruence fails, unfold
      -- the wrapper below and compare its values instead.
      catch ex =>
        if f.isConstOf ``Eq || f.isConstOf ``Shrink ||
            f.isConstOf ``CategoryStruct.comp || f.isConstOf ``CategoryTheory.Functor.map ||
            f.isConstOf ``CategoryTheory.Functor.obj ||
            f.isConstOf ``CategoryTheory.inv then throw ex
        set init
    let lhs' ← whnf lhs
    let rhs' ← whnf rhs
    if lhs' != lhs || rhs' != rhs then
      return ← pretraceHEq lhs' rhs' next
    let lhs' := (← unfoldDefinition? lhs).getD lhs
    let rhs' := (← unfoldDefinition? rhs).getD rhs
    if lhs' != lhs || rhs' != rhs then
      return ← pretraceHEq lhs' rhs' next
    throwError "coefficient congruence stuck:
{lhs}
{rhs}"
  let h ← prove
  -- Preserve the original endpoints after explicit definitional reductions.
  -- The kernel checks the identity application's argument at this exact type.
  let expected ← mkHEq lhs rhs
  let h ← if (← inferType h) == expected then pure h else
    pure (mkApp2 (mkConst ``id [.zero]) expected h)
  modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
  return h

private meta def pretraceZeta (e : Expr) : MetaM Expr := do
  let mut values : Array (FVarId × Expr) := #[]
  let subst (e : Expr) (values : Array (FVarId × Expr)) : Expr :=
    e.replace fun sub => do
      let .fvar id := sub | none
      (values.find? (fun pair => pair.1 == id)).map Prod.snd
  for decl in (← getLCtx) do
    if let some value := decl.value? then
      let value ← instantiateMVars value
      values := values.push (decl.fvarId, subst value values)
  return subst (← instantiateMVars e) values

private meta def pretraceFastDefEq (a b : Expr) : MetaM Bool := do
  if a.hasMVar || b.hasMVar || a.hasLevelMVar || b.hasLevelMVar then return false
  let saved ← getMCtx
  let ticks ← IO.getNumHeartbeats
  let result ← try
    withTheReader Core.Context (fun ctx =>
        { ctx with initHeartbeats := ticks, maxHeartbeats := 2000000 }) do
      withTransparency .all <| isDefEq a b
    catch _ => pure false
  setMCtx saved
  return result

private meta def pretraceRepairSpine (value : Expr) :
    StateRefT PretraceCongrState MetaM Expr := do
  let mut f := value.getAppFn
  for a in value.getAppArgs do
    let ty ← whnf (← inferType f)
    unless ty.isForall do throwError "expected a function in checked application"
    let actual ← pretraceZeta (← inferType a)
    let expected ← pretraceZeta ty.bindingDomain!
    let direct ← if actual == expected then pure true else
      pretraceFastDefEq actual expected
    let a ← if direct then pure a else do
      let h ← mkEqOfHEq (← pretraceHEq actual expected)
      mkAppM ``Eq.mp #[h, a]
    f := mkApp f a
  return f

private meta def pretraceFinish (h : Syntax) : TacticM Unit := withMainContext do
  let value ← Elab.Term.elabTerm h none
  liftMetaTactic fun goal => goal.withContext do
    let source ← instantiateMVars (← pretraceZeta (← whnf (← inferType value)))
    let target ← instantiateMVars (← pretraceZeta (← whnf (← goal.getType)))
    if source == target then
      goal.assign value
      return []
    let some (_, lhs, rhs) := source.eq? | throwError "expected source equality"
    let some (_, lhs', rhs') := target.eq? | throwError "expected target equality"
    let (hL, st) ← (pretraceHEq lhs lhs').run {}
    let (hR, _) ← (pretraceHEq rhs rhs').run st
    let hL ← mkAppM ``HEq.symm #[hL]
    let h ← mkAppM ``heq_of_eq #[value]
    let h ← mkAppM ``HEq.trans #[h, hR]
    let h ← mkAppM ``HEq.trans #[hL, h]
    goal.assign (← mkAppM ``eq_of_heq #[h])
    return []

private meta def pretraceCheckedFinish (h : Syntax) : TacticM Unit := withMainContext do
  let raw ← Elab.Term.elabTerm h none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let raw ← instantiateMVars raw
  let (value, st₀) ← (pretraceRepairSpine raw).run {}
  liftMetaTactic fun goal => goal.withContext do
    let source ← instantiateMVars (← pretraceZeta (← whnf (← inferType value)))
    let target ← instantiateMVars (← pretraceZeta (← whnf (← goal.getType)))
    if source == target then
      goal.assign value
      return []
    let some (_, lhs, rhs) := source.eq? | throwError "expected source equality"
    let some (_, lhs', rhs') := target.eq? | throwError "expected target equality"
    let (hL, st) ← (pretraceHEq lhs lhs').run st₀
    let (hR, _) ← (pretraceHEq rhs rhs').run st
    let hL ← mkAppM ``HEq.symm #[hL]
    let h ← mkAppM ``heq_of_eq #[value]
    let h ← mkAppM ``HEq.trans #[h, hR]
    let h ← mkAppM ``HEq.trans #[hL, h]
    goal.assign (← mkAppM ``eq_of_heq #[h])
    return []

private meta def pretraceCongrGoal : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← goal.getType).eq? | throwError "expected equality"
  let (h, _) ← (pretraceHEq lhs rhs).run {}
  goal.assign (← mkEqOfHEq h)
  replaceMainGoal []

private meta def pretraceExact (t : Syntax) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let value ← Elab.Term.elabTerm t none
  let actual ← pretraceZeta (← inferType value)
  let target ← pretraceZeta (← goal.getType)
  if actual == target then
    goal.assign value
    replaceMainGoal []
    return
  let (h, _) ← (pretraceHEq actual target).run {}
  let h ← mkEqOfHEq h
  goal.assign (← mkAppM ``Eq.mp #[h, value])
  replaceMainGoal []

private meta def pretraceExactRaw (t : Syntax) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let value ← Elab.Term.elabTerm t none
  let actual ← inferType value
  let target ← goal.getType
  let (h, _) ← (pretraceHEq actual target).run {}
  goal.assign (← mkAppM ``Eq.mp #[← mkEqOfHEq h, value])
  replaceMainGoal []

private theorem map_inverse_hom
    {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    R.map (inv f) ≫ R.map f = 𝟙 _ := by
  rw [← R.map_comp, IsIso.inv_hom_id, R.map_id]

private theorem map_iso_hom_inv
    {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {X Y : C} (e : X ≅ Y) :
    R.map e.hom ≫ R.map e.inv = 𝟙 _ := by
  rw [← R.map_comp, e.hom_inv_id, R.map_id]

private theorem cancel_plain_prefix
    {C : Type*} [Category C] {X Y HX HY Z Z' : C}
    {β : X ⟶ Y} {a : X ⟶ HX} {ia : HX ⟶ X} {b : Y ⟶ HY} {ib : HY ⟶ Y}
    {h : HX ⟶ HY} {ih : HY ⟶ HX} {r : Y ⟶ Z} {τ : HY ⟶ Z'}
    {it : Z' ⟶ HY} {u : Z ⟶ Z'} {iu : Z' ⟶ Z}
    (hn : β ≫ b = a ≫ h) (ht : τ = ib ≫ r ≫ u)
    (ha : ia ≫ a = 𝟙 HX) (hb : b ≫ ib = 𝟙 Y)
    (htt : it ≫ τ = 𝟙 Z') (hh : ih ≫ h = 𝟙 HY) (hu : u ≫ iu = 𝟙 Z) :
    (u ≫ it ≫ ih) ≫ ia ≫ (β ≫ r) = 𝟙 Z := by
  have hr : r = b ≫ τ ≫ iu := by
    rw [ht]
    simp only [Category.assoc, reassoc_of% hb, hu, Category.comp_id]
  rw [hr]
  simp only [Category.assoc, reassoc_of% hn, reassoc_of% ha,
    reassoc_of% hh, reassoc_of% htt, hu]

private theorem map_prefix_inverse
    {C D : Type*} [Category C] [Category D] {R : C ⥤ D}
    {A B Q : C} {a : A ⟶ B} {t : B ⟶ Q} {y : Q ⟶ A}
    (h : a ≫ t ≫ y = 𝟙 A) : R.map a ≫ R.map t ≫ R.map y = 𝟙 _ := by
  simpa only [R.map_comp, R.map_id, Category.assoc] using congrArg R.map h

private theorem insert_inverse_prefix
    {D : Type*} [Category D] {A B P Q : D}
    {a : A ⟶ B} {t : B ⟶ Q} {y : Q ⟶ A} {q : P ⟶ Q} [IsIso q]
    (h : a ≫ t ≫ y = 𝟙 A) : (a ≫ (t ≫ inv q)) ≫ q ≫ y = 𝟙 A := by
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using h

private theorem map_hom_inverse
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {X Y : C} (p : X ⟶ Y) [IsIso p] : R.map p ≫ R.map (inv p) = 𝟙 _ := by
  rw [← R.map_comp, IsIso.hom_inv_id, R.map_id]

private theorem cancel_split_plain_route
    {D : Type*} [Category D] {A B P Q W X V O : D}
    {a : A ⟶ B} {t : B ⟶ P} {q : P ⟶ Q} {y : Q ⟶ A}
    {κ : A ⟶ W} {j : P ⟶ X} {x : X ⟶ V} {p : V ⟶ W}
    {pi : W ⟶ V} {v : V ⟶ O}
    (hr : q ≫ y ≫ κ = j ≫ x ≫ p)
    (hl : (a ≫ t) ≫ q ≫ y = 𝟙 A) (hp : p ≫ pi = 𝟙 V) :
    a ≫ t ≫ j ≫ x ≫ v = κ ≫ pi ≫ v := by
  calc
    _ = (a ≫ t) ≫ (j ≫ x ≫ p) ≫ pi ≫ v := by
      simp only [Category.assoc, reassoc_of% hp]
    _ = (a ≫ t) ≫ (q ≫ y ≫ κ) ≫ pi ≫ v := by rw [hr]
    _ = _ := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun z ↦ z ≫ κ ≫ pi ≫ v) hl

private theorem cancel_split_route_no_suffix
    {D : Type*} [Category D] {A B P Q W X V : D}
    {a : A ⟶ B} {t : B ⟶ P} {q : P ⟶ Q} {y : Q ⟶ A}
    {κ : A ⟶ W} {j : P ⟶ X} {x : X ⟶ V} {p : V ⟶ W} {pi : W ⟶ V}
    (hr : q ≫ y ≫ κ = j ≫ x ≫ p)
    (hl : (a ≫ t) ≫ q ≫ y = 𝟙 A) (hp : p ≫ pi = 𝟙 V) :
    a ≫ t ≫ j ≫ x = κ ≫ pi := by
  simpa only [Category.comp_id] using
    (cancel_split_plain_route (v := 𝟙 V) hr hl hp)

private theorem postcompose_route_suffix
    {C D : Type*} [Category C] [Category D] {R : C ⥤ D}
    {X Y Z : C} {P Q A B : D}
    {a : P ⟶ Q} {t : Q ⟶ A} {j : A ⟶ B} {x : B ⟶ R.obj Y}
    {κ : P ⟶ R.obj X} {p : X ⟶ Y}
    (h : a ≫ t ≫ j ≫ x = κ ≫ R.map p) (v : Y ⟶ Z) :
    a ≫ t ≫ j ≫ x ≫ R.map v = κ ≫ R.map (p ≫ v) := by
  simpa only [R.map_comp, Category.assoc] using
    congrArg (fun z ↦ z ≫ R.map v) h

private theorem normalize_twist_formula
    {C D : Type*} [Category C] [Category D] {U : C ⥤ D}
    {A B : D} {X Y Z : C} {τ : A ⟶ U.obj Z} {a : A ⟶ B}
    {b : B ⟶ U.obj X} {c : X ⟶ Y} {w : Y ⟶ Z}
    (h : τ = a ≫ b ≫ U.map (c ≫ w)) :
    τ = a ≫ (b ≫ U.map c) ≫ U.map w := by
  simpa only [U.map_comp, Category.assoc] using h

private theorem cancel_functor_route
    {C D : Type*} [Category C] [Category D] {R : C ⥤ D}
    {A B Q X V W O : C} {P : D}
    {a : A ⟶ B} {t : B ⟶ Q} {y : Q ⟶ A}
    {q : P ⟶ R.obj Q} [IsIso q]
    {κ : R.obj A ⟶ R.obj W} {j : P ⟶ R.obj X}
    {x : X ⟶ V} {p : V ⟶ W} [IsIso p]
    (hinv : a ≫ t ≫ y = 𝟙 A)
    (hroute : q ≫ R.map y ≫ κ = j ≫ R.map (x ≫ p)) (v : V ⟶ O) :
    R.map a ≫ (R.map t ≫ inv q) ≫ j ≫ R.map x ≫ R.map v =
      κ ≫ R.map (inv p ≫ v) := by
  have hm := map_prefix_inverse (R := R) hinv
  have hpre := insert_inverse_prefix (q := q) hm
  have hpi := map_hom_inverse R p
  have hs : q ≫ R.map y ≫ κ = j ≫ R.map x ≫ R.map p := by
    simpa only [R.map_comp, Category.assoc] using hroute
  have hc := cancel_split_route_no_suffix hs hpre hpi
  exact postcompose_route_suffix hc v

@[irreducible]
private def pretraceAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleObjectDerivedPullback Λ f ⊣ moduleObjectDerivedPushforward Λ f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

private def nativeTensorNat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor (DerivedCategory (Modules Λ Y)) ⋙ moduleObjectDerivedPullback Λ f ⟶
      ((moduleObjectDerivedPullback Λ f).prod (moduleObjectDerivedPullback Λ f)) ⋙
        tensor (DerivedCategory (Modules Λ X)) where
  app Z := (nativeProjectionTensorIso Λ f Z.1 Z.2).hom
  naturality Z Z' g := by
    unfold nativeProjectionTensorIso traceTensorComparison
    dsimp only [Iso.app, asIso, id, Functor.comp_map, Functor.prod_map, tensor_map]
    unfold moduleObjectDerivedTensorComparison
    exact (leftDerivedUpperStarTensor_naturality Λ f g.1 g.2).symm

private theorem native_square_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (K L : DerivedCategory (Modules Λ Y)) :
    let f := ProjectiveLine Y ↘ Y
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let B := moduleObjectDerivedPullback Λ (secondProjection Y)
    let F := moduleObjectDerivedPullback Λ f
    let s := ambientPullbackComparison Λ (square Y)
    s.hom.app (K ⊗ L) ≫ A.map ((nativeTensorNat Λ f).app (K, L)) ≫
        (nativeTensorNat Λ (firstProjection Y)).app (F.obj K, F.obj L) =
      B.map ((nativeTensorNat Λ f).app (K, L)) ≫
        (nativeTensorNat Λ (secondProjection Y)).app (F.obj K, F.obj L) ≫
          tensorHom (s.hom.app K) (s.hom.app L) := by
  dsimp only
  have hc := pullbackSquareComparison_tensor Λ (square Y).toCommSq K L
  rw [pullbackSquareComparison_eq] at hc
  unfold nativeTensorNat nativeProjectionTensorIso traceTensorComparison
  unfold ambientPullbackComparison moduleObjectDerivedPullback
  dsimp only [Iso.app, asIso, id]
  unfold moduleObjectDerivedTensorComparison condensedAmbientPullbackComparison
  section_evaluation_exact hc.symm

private theorem native_left_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules Λ Y)) (N : DerivedCategory (Modules Λ X)) :
    projectionMap Λ f K N = (pretraceAdjunction Λ f).homEquiv _ _
      ((nativeProjectionTensorIso Λ f K ((moduleObjectDerivedPushforward Λ f).obj N)).hom ≫
        tensorHom (𝟙 _) ((pretraceAdjunction Λ f).counit.app N)) := by
  have h := normalized_projection_transpose Λ (projection_existsUnique Λ).exists.choose
    (projection_existsUnique Λ).exists.choose_spec f K N
  unfold projectionMap
  apply eq_of_heq
  refine h.trans ?_
  unfold traceProjectionFromComparison traceAdjunction pretraceAdjunction tracePull tracePush
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  dsimp only [id, Functor.id_obj]
  section_evaluation_exact (HEq.refl
      ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
        ((nativeProjectionTensorIso Λ f K
          ((moduleObjectDerivedPushforward Λ f).obj N)).hom ≫
          tensorHom (𝟙 _)
            ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app N))))

private theorem right_projection_formula
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor D))
    (N : D) (K : C) :
    ((a.rightAdjointProjectionMap δ).app N).app K = a.homEquiv _ _
      ((δ.app (G.obj N)).app K ≫ tensorHom (a.counit.app N) (𝟙 _)) := by
  simp only [Adjunction.rightAdjointProjectionMap_app_app, curriedTensor_map_app,
    tensorHom_id, curriedTensor_obj_obj, Functor.id_obj]

private theorem native_right_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : DerivedCategory (Modules Λ X)) (K : DerivedCategory (Modules Λ Y)) :
    projectionMateMap Λ f N K = (pretraceAdjunction Λ f).homEquiv _ _
      ((nativeProjectionTensorIso Λ f ((moduleObjectDerivedPushforward Λ f).obj N) K).hom ≫
        tensorHom ((pretraceAdjunction Λ f).counit.app N) (𝟙 _)) := by
  have h := (projectionMate_existsUnique Λ).exists.choose_spec f N K
  unfold ProjectionMateNormalized at h
  unfold projectionMateMap
  apply eq_of_heq
  refine h.trans ?_
  unfold nativeProjectionTensorIso traceTensorComparison pretraceAdjunction
  dsimp only [id, Iso.app, asIso]
  section_evaluation_exact (heq_of_eq
    (right_projection_formula (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
      (moduleObjectDerivedTensorComparison Λ f) N K))

private theorem monoidal_kunneth
    {C D V : Type*} [Category C] [Category D] [Category V]
    [mc : MonoidalCategory C] [md : MonoidalCategory D]
    [mv : MonoidalCategory V]
    {F : C ⥤ D} {P : D ⥤ C} {U₁ U₂ : D ⥤ V} {Q₁ Q₂ : V ⥤ D}
    (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
    (d : tensor C ⋙ F ⟶ (F.prod F) ⋙ tensor D)
    (d₁ : tensor D ⋙ U₁ ⟶ (U₁.prod U₁) ⋙ tensor V)
    (d₂ : tensor D ⋙ U₂ ⟶ (U₂.prod U₂) ⋙ tensor V)
    (s : F ⋙ U₂ ≅ F ⋙ U₁)
    (hs : ∀ K L : C,
      s.hom.app (K ⊗ L) ≫ U₁.map (d.app (K, L)) ≫
          d₁.app (F.obj K, F.obj L) =
        U₂.map (d.app (K, L)) ≫ d₂.app (F.obj K, F.obj L) ≫
          tensorHom (s.hom.app K) (s.hom.app L))
    (M N : D) :
    a.homEquiv _ _ (d.app (P.obj M, P.obj N) ≫ tensorHom (𝟙 _) (a.counit.app N)) ≫
      P.map (((traceAbstractMate a a₂ s).app M ▷ N) ≫
        a₂.homEquiv _ _ (d₂.app (Q₂.obj (U₁.obj M), N) ≫
          tensorHom (a₂.counit.app (U₁.obj M)) (𝟙 _))) ≫
      (conjugateIsoEquiv (a.comp a₂) (a.comp a₁) s.symm).hom.app
        (U₁.obj M ⊗ U₂.obj N) =
    a.homEquiv _ _ (d.app (P.obj M, P.obj N) ≫ tensorHom (a.counit.app M) (𝟙 _)) ≫
      P.map ((M ◁ (traceAbstractMate a a₁ s.symm).app N) ≫
        a₁.homEquiv _ _ (d₁.app (M, Q₁.obj (U₂.obj N)) ≫
          tensorHom (𝟙 _) (a₁.counit.app (U₂.obj N)))) := by
  have h := kunneth_factorization a a₁ a₂ (tensor C) (tensor D) (tensor V)
    d d₁ d₂ s (fun K L ↦ by simpa only [tensor_obj, tensor_map] using hs K L) M N
  dsimp only [CategoryTheory.Functor.prod, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj, tensor_obj, tensor_map] at h ⊢
  simpa only [tensorHom_id, id_tensorHom] using h

private theorem normalized_kunneth
    {C D V : Type*} [Category C] [Category D] [Category V]
    [mc : MonoidalCategory C] [md : MonoidalCategory D]
    [mv : MonoidalCategory V]
    {F : C ⥤ D} {P : D ⥤ C} {U₁ U₂ : D ⥤ V} {Q₁ Q₂ : V ⥤ D}
    (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
    (d : tensor C ⋙ F ⟶ (F.prod F) ⋙ tensor D)
    (d₁ : tensor D ⋙ U₁ ⟶ (U₁.prod U₁) ⋙ tensor V)
    (d₂ : tensor D ⋙ U₂ ⟶ (U₂.prod U₂) ⋙ tensor V)
    (s : F ⋙ U₂ ≅ F ⋙ U₁)
    (hs : ∀ K L : C,
      s.hom.app (K ⊗ L) ≫ U₁.map (d.app (K, L)) ≫
          d₁.app (F.obj K, F.obj L) =
        U₂.map (d.app (K, L)) ≫ d₂.app (F.obj K, F.obj L) ≫
          tensorHom (s.hom.app K) (s.hom.app L))
    (M N : D)
    (q : P.obj M ⊗ P.obj N ⟶ P.obj (F.obj (P.obj M) ⊗ N))
    (r : Q₂.obj (U₁.obj M) ⊗ N ⟶ Q₂.obj (U₁.obj M ⊗ U₂.obj N))
    (j : P.obj M ⊗ P.obj N ⟶ P.obj (M ⊗ F.obj (P.obj N)))
    (p : M ⊗ Q₁.obj (U₂.obj N) ⟶ Q₁.obj (U₁.obj M ⊗ U₂.obj N))
    (b : F.obj (P.obj M) ⟶ Q₂.obj (U₁.obj M))
    (e : F.obj (P.obj N) ⟶ Q₁.obj (U₂.obj N))
    (κ : P.obj (Q₂.obj (U₁.obj M ⊗ U₂.obj N)) ⟶
      P.obj (Q₁.obj (U₁.obj M ⊗ U₂.obj N)))
    (β : F.obj (P.obj M) ⊗ N ⟶ Q₂.obj (U₁.obj M) ⊗ N)
    (ε : M ⊗ F.obj (P.obj N) ⟶ M ⊗ Q₁.obj (U₂.obj N))
    (hq : q = a.homEquiv _ _ (d.app (P.obj M, P.obj N) ≫
      tensorHom (𝟙 _) (a.counit.app N)))
    (hr : r = a₂.homEquiv _ _ (d₂.app (Q₂.obj (U₁.obj M), N) ≫
      tensorHom (a₂.counit.app (U₁.obj M)) (𝟙 _)))
    (hj : j = a.homEquiv _ _ (d.app (P.obj M, P.obj N) ≫
      tensorHom (a.counit.app M) (𝟙 _)))
    (hp : p = a₁.homEquiv _ _ (d₁.app (M, Q₁.obj (U₂.obj N)) ≫
      tensorHom (𝟙 _) (a₁.counit.app (U₂.obj N))))
    (hb : b = (traceAbstractMate a a₂ s).app M)
    (he : e = (traceAbstractMate a a₁ s.symm).app N)
    (hκ : κ = (conjugateIsoEquiv (a.comp a₂) (a.comp a₁) s.symm).hom.app
      (U₁.obj M ⊗ U₂.obj N))
    (hβ : β = b ▷ N) (hε : ε = M ◁ e) :
    q ≫ P.map (β ≫ r) ≫ κ = j ≫ P.map (ε ≫ p) := by
  rw [hβ, hε, hq, hr, hj, hp, hb, he, hκ]
  exact monoidal_kunneth a a₁ a₂ d d₁ d₂ s hs M N

private theorem conjugate_symm_hom
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} {R S : D ⥤ C} (a : F ⊣ R) (b : G ⊣ S) (s : G ≅ F) :
    (conjugateIsoEquiv b a s.symm).hom = (conjugateIsoEquiv a b s).inv := by
  rfl

private theorem pretrace_path_naturality
    {C D V : Type*} [Category C] [Category D] [Category V]
    {R : D ⥤ C} {U S : V ⥤ D} (s : U ⋙ R ≅ S ⋙ R)
    {X Y : V} (f : X ⟶ Y) :
    R.map (U.map f) ≫ s.hom.app Y = s.hom.app X ≫ R.map (S.map f) := by
  exact s.hom.naturality f

private theorem comp_map_id
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X : C} {Z : D} (m : Z ⟶ G.obj X) : m = m ≫ G.map (𝟙 X) := by
  rw [G.map_id, Category.comp_id]

private theorem native_forward_mate_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    traceAbstractMate (pretraceAdjunction Λ (ProjectiveLine Y ↘ Y))
      (pretraceAdjunction Λ (secondProjection Y))
      (ambientPullbackComparison Λ (square Y)) =
      condensedAmbientExchange Λ (square Y) := by
  unfold traceAbstractMate pretraceAdjunction ambientPullbackComparison
    condensedAmbientExchange moduleObjectDerivedPullback moduleObjectDerivedPushforward
  rfl

private theorem native_forward_mate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (traceAbstractMate (pretraceAdjunction Λ (ProjectiveLine Y ↘ Y))
      (pretraceAdjunction Λ (secondProjection Y))
      (ambientPullbackComparison Λ (square Y))).app M = secondPretraceExchangeMap Λ Y M := by
  have h := congrArg (fun z ↦ z.app M) (native_forward_mate_nat Λ Y)
  unfold secondPretraceExchangeMap
  run_tac pretraceFinish (Lean.mkIdent `h)

private theorem native_opposite_mate_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    traceAbstractMate (pretraceAdjunction Λ (ProjectiveLine Y ↘ Y))
      (pretraceAdjunction Λ (firstProjection Y))
      (ambientPullbackComparison Λ (square Y)).symm =
      (mateEquiv
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y))
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y))
        (TwoSquare.mk _ _ _ _
          (condensedAmbientPullbackComparison Λ (square Y)).inv)).natTrans := by
  unfold traceAbstractMate pretraceAdjunction ambientPullbackComparison
    moduleObjectDerivedPullback moduleObjectDerivedPushforward
  rfl

private theorem native_opposite_mate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (N : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (traceAbstractMate (pretraceAdjunction Λ (ProjectiveLine Y ↘ Y))
      (pretraceAdjunction Λ (firstProjection Y))
      (ambientPullbackComparison Λ (square Y)).symm).app N =
      firstTraceExchange Λ Y N
        ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N) (Iso.refl _) := by
  have h := congrArg (fun z ↦ z.app N) (native_opposite_mate_nat Λ Y)
  have h' := h.trans (comp_map_id
    (CondensedRing.lowerStar Λ (firstProjection Y)).rightDerivedFunctor _)
  unfold firstTraceExchange
  run_tac pretraceFinish (Lean.mkIdent `h')

private theorem native_path_mate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    : (conjugateIsoEquiv
      ((pretraceAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
        (pretraceAdjunction Λ (secondProjection Y)))
      ((pretraceAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
        (pretraceAdjunction Λ (firstProjection Y)))
      (ambientPullbackComparison Λ (square Y)).symm).hom =
      (firstPathComparison Λ Y).hom := by
  let f := ProjectiveLine Y ↘ Y
  let a := pretraceAdjunction Λ f
  let a₁ := pretraceAdjunction Λ (firstProjection Y)
  let a₂ := pretraceAdjunction Λ (secondProjection Y)
  let s := ambientPullbackComparison Λ (square Y)
  have hi := conjugate_symm_hom (a.comp a₁) (a.comp a₂) s
  dsimp only [a, a₁, a₂, s, f] at hi
  unfold pretraceAdjunction ambientPullbackComparison at hi ⊢
  unfold firstPathComparison
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward at hi ⊢
  dsimp only [id, Iso.symm_hom] at hi ⊢
  run_tac pretraceFinish (Lean.mkIdent `hi)

private theorem native_left_projection_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules Λ Y)) (N : DerivedCategory (Modules Λ X)) :
    projectionMap Λ f K N = (pretraceAdjunction Λ f).homEquiv _ _
      ((nativeTensorNat Λ f).app (K, (moduleObjectDerivedPushforward Λ f).obj N) ≫
        tensorHom (𝟙 _) ((pretraceAdjunction Λ f).counit.app N)) := by
  unfold nativeTensorNat
  dsimp only [NatTrans.app, CategoryTheory.Functor.prod, Functor.comp_obj,
    Functor.id_obj, tensor_obj]
  have h := native_left_projection Λ f K N
  dsimp only [Functor.id_obj] at h
  run_tac pretraceFinish (Lean.mkIdent `h)

private theorem native_right_projection_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : DerivedCategory (Modules Λ X)) (K : DerivedCategory (Modules Λ Y)) :
    projectionMateMap Λ f N K = (pretraceAdjunction Λ f).homEquiv _ _
      ((nativeTensorNat Λ f).app ((moduleObjectDerivedPushforward Λ f).obj N, K) ≫
        tensorHom ((pretraceAdjunction Λ f).counit.app N) (𝟙 _)) := by
  unfold nativeTensorNat
  dsimp only [NatTrans.app, CategoryTheory.Functor.prod, Functor.comp_obj,
    Functor.id_obj, tensor_obj]
  have h := native_right_projection Λ f N K
  run_tac pretraceFinish (Lean.mkIdent `h)

private theorem native_path_mate_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (Z : DerivedCategory (Modules Λ (diagonalSurface Y))) :
    (firstPathComparison Λ Y).hom.app Z =
      (conjugateIsoEquiv
        ((pretraceAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
          (pretraceAdjunction Λ (secondProjection Y)))
        ((pretraceAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
          (pretraceAdjunction Λ (firstProjection Y)))
        (ambientPullbackComparison Λ (square Y)).symm).hom.app Z := by
  have h := (congrArg (fun z ↦ z.app Z) (native_path_mate Λ Y)).symm
  run_tac pretraceFinish (Lean.mkIdent `h)

private theorem native_kunneth
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M N : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    let f := ProjectiveLine Y ↘ Y
    let R := moduleObjectDerivedPushforward Λ f
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let B := moduleObjectDerivedPullback Λ (secondProjection Y)
    projectionMap Λ f (R.obj M) N ≫
      R.map ((secondPretraceExchangeMap Λ Y M ▷ N) ≫
        projectionMateMap Λ (secondProjection Y) (A.obj M) N) ≫
      (firstPathComparison Λ Y).hom.app (A.obj M ⊗ B.obj N) =
    projectionMateMap Λ f M (R.obj N) ≫
      R.map ((M ◁ firstTraceExchange Λ Y N (B.obj N) (Iso.refl _)) ≫
        projectionMap Λ (firstProjection Y) M (B.obj N)) := by
  intro f R A B
  have h := normalized_kunneth
    (pretraceAdjunction Λ (ProjectiveLine Y ↘ Y))
    (pretraceAdjunction Λ (firstProjection Y))
    (pretraceAdjunction Λ (secondProjection Y))
    (nativeTensorNat Λ (ProjectiveLine Y ↘ Y)) (nativeTensorNat Λ (firstProjection Y))
    (nativeTensorNat Λ (secondProjection Y)) (ambientPullbackComparison Λ (square Y))
    (fun K L ↦ by
      have h := native_square_tensor Λ Y K L
      run_tac pretraceFinish (Lean.mkIdent `h)) M N
    (projectionMap Λ (ProjectiveLine Y ↘ Y)
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) N)
    (projectionMateMap Λ (secondProjection Y)
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) N)
    (projectionMateMap Λ (ProjectiveLine Y ↘ Y) M
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj N))
    (projectionMap Λ (firstProjection Y) M
      ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N))
    (secondPretraceExchangeMap Λ Y M)
    (firstTraceExchange Λ Y N
      ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N) (Iso.refl _))
    ((firstPathComparison Λ Y).hom.app
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
        (moduleObjectDerivedPullback Λ (secondProjection Y)).obj N))
    (secondPretraceExchangeMap Λ Y M ▷ N)
    (M ◁ firstTraceExchange Λ Y N
      ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N) (Iso.refl _))
    (by
      have h := native_left_projection_nat Λ (ProjectiveLine Y ↘ Y)
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) N
      run_tac pretraceFinish (Lean.mkIdent `h))
    (by
      have h := native_right_projection_nat Λ (secondProjection Y)
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) N
      run_tac pretraceFinish (Lean.mkIdent `h))
    (by
      have h := native_right_projection_nat Λ (ProjectiveLine Y ↘ Y) M
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj N)
      run_tac pretraceFinish (Lean.mkIdent `h))
    (by
      have h := native_left_projection_nat Λ (firstProjection Y) M
        ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N)
      run_tac pretraceFinish (Lean.mkIdent `h))
    (by
      have h := (native_forward_mate Λ Y M).symm
      run_tac pretraceFinish (Lean.mkIdent `h))
    (by
      have h := (native_opposite_mate Λ Y N).symm
      run_tac pretraceFinish (Lean.mkIdent `h))
    (by
      have h := native_path_mate_app Λ Y
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
          (moduleObjectDerivedPullback Λ (secondProjection Y)).obj N)
      run_tac pretraceFinish (Lean.mkIdent `h))
    (by
      rfl) (by rfl)
  run_tac pretraceFinish (Lean.mkIdent `h)

private theorem route_transport_of_equations
    {C D : Type*} [Category C] [Category D] {R : D ⥤ C}
    {L K K' E B B' F F' : D} {P : C}
    {q : P ⟶ R.obj L} {r : L ⟶ K} {u : K ⟶ K'}
    {κ : R.obj K ⟶ R.obj F} {κ' : R.obj K' ⟶ R.obj F'}
    {j : P ⟶ R.obj E} {m₀ : E ⟶ B} {m : E ⟶ B'} {g : B ⟶ B'}
    {p₀ : B ⟶ F} {p : B' ⟶ F'} {s : F ⟶ F'}
    (hk : q ≫ R.map r ≫ κ = j ≫ R.map (m₀ ≫ p₀))
    (hn : R.map u ≫ κ' = κ ≫ R.map s)
    (hm : m = m₀ ≫ g) (hp : g ≫ p = p₀ ≫ s) :
    q ≫ R.map (r ≫ u) ≫ κ' = j ≫ R.map (m ≫ p) := by
  have h := congrArg (fun z ↦ z ≫ R.map s) hk
  simp only [R.map_comp, Category.assoc] at h ⊢
  rw [← hn] at h
  have hp' := congrArg R.map hp
  simp only [R.map_comp] at hp'
  rw [← hp'] at h
  rw [hm, R.map_comp]
  simpa only [R.map_comp, Category.assoc] using h

private theorem pretrace_functor_route
    {C D : Type*} [Category C] [Category D] {R : D ⥤ C}
    {L B K K' E V V' F F' : D} {P : C}
    {q : P ⟶ R.obj L} {β : L ⟶ B} {r : B ⟶ K} {u : K ⟶ K'}
    {κ : R.obj K ⟶ R.obj F} {κ' : R.obj K' ⟶ R.obj F'}
    {j : P ⟶ R.obj E} {m₀ : E ⟶ V} {m : E ⟶ V'} {g : V ⟶ V'}
    {p₀ : V ⟶ F} {p : V' ⟶ F'} {s : F ⟶ F'}
    (hk : q ≫ R.map (β ≫ r) ≫ κ = j ≫ R.map (m₀ ≫ p₀))
    (hn : R.map u ≫ κ' = κ ≫ R.map s)
    (hm : m = m₀ ≫ g) (hp : g ≫ p = p₀ ≫ s) :
    q ≫ R.map (β ≫ r ≫ u) ≫ κ' = j ≫ R.map (m ≫ p) := by
  have h := route_transport_of_equations hk hn hm hp
  simpa only [Category.assoc] using h

private theorem exchange_comp_of_formula
    {C D : Type*} [Category C] [Category D] {G : C ⥤ D}
    {B T : C} {X : D} {e : B ≅ T} {χ : X ⟶ G.obj B}
    {m : X ⟶ G.obj T} {m₀ : X ⟶ G.obj B}
    (h : m = χ ≫ G.map e.hom)
    (h₀ : m₀ = χ ≫ G.map (Iso.refl B).hom) :
    m = m₀ ≫ G.map e.hom := by
  rw [h, h₀]
  simp only [Iso.refl_hom, G.map_id, Category.comp_id]

private theorem native_exchange_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (N : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (T : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj N ≅ T) :
    firstTraceExchange Λ Y N T e =
      firstTraceExchange Λ Y N
        ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N) (Iso.refl _) ≫
          (moduleObjectDerivedPushforward Λ (firstProjection Y)).map e.hom := by
  have h := firstTraceExchange_eq Λ Y N T e
  have h₀ := firstTraceExchange_eq Λ Y N
    ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N) (Iso.refl _)
  have hh := exchange_comp_of_formula h h₀
  run_tac pretraceFinish (Lean.mkIdent `hh)

private theorem native_projection_line_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M N : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (T : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj N ≅ T) :
    (M ◁ (moduleObjectDerivedPushforward Λ (firstProjection Y)).map e.hom) ≫
        projectionMap Λ (firstProjection Y) M T =
      projectionMap Λ (firstProjection Y) M
          ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N) ≫
        (moduleObjectDerivedPushforward Λ (firstProjection Y)).map
          (((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) ◁ e.hom) := by
  have h := projectionMap_naturality_right Λ (firstProjection Y) M e.hom
  run_tac pretraceFinish (Lean.mkIdent `h)

private theorem native_whisker_exchange_line
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M N : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (T : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj N ≅ T) :
    (M ◁ firstTraceExchange Λ Y N T e) =
      (M ◁ firstTraceExchange Λ Y N
        ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj N) (Iso.refl _)) ≫
        (M ◁ (moduleObjectDerivedPushforward Λ (firstProjection Y)).map e.hom) := by
  have h := congrArg (fun z ↦ M ◁ z) (native_exchange_comp Λ Y N T e)
  simp only [whiskerLeft_comp] at h
  run_tac pretraceFinish (Lean.mkIdent `h)

private theorem native_path_line_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M N : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (T : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj N ≅ T) :
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
    let S := moduleObjectDerivedPushforward Λ (firstProjection Y)
    R.map (U.map (A.obj M ◁ e.hom)) ≫
        (firstPathComparison Λ Y).hom.app (A.obj M ⊗ T) =
      (firstPathComparison Λ Y).hom.app
          (A.obj M ⊗ (moduleObjectDerivedPullback Λ (secondProjection Y)).obj N) ≫
        R.map (S.map (A.obj M ◁ e.hom)) := by
  intro R A U S
  let c := A.obj M ◁ e.hom
  run_tac do
    let stx ← `($(Lean.mkIdent `pretrace_path_naturality)
      ($(Lean.mkIdent `firstPathComparison) $(Lean.mkIdent `Λ) $(Lean.mkIdent `Y))
      $(Lean.mkIdent `c))
    pretraceCheckedFinish stx

private theorem native_kunneth_line
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M N : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (T : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj N ≅ T) :
    let f := ProjectiveLine Y ↘ Y
    let R := moduleObjectDerivedPushforward Λ f
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    projectionMap Λ f (R.obj M) N ≫
      R.map ((secondPretraceExchangeMap Λ Y M ▷ N) ≫
        projectionMateMap Λ (secondProjection Y) (A.obj M) N ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map (A.obj M ◁ e.hom)) ≫
      (firstPathComparison Λ Y).hom.app (A.obj M ⊗ T) =
    projectionMateMap Λ f M (R.obj N) ≫
      R.map ((M ◁ firstTraceExchange Λ Y N T e) ≫
        projectionMap Λ (firstProjection Y) M T) := by
  intro f R A
  have hK := native_kunneth Λ Y M N
  have hn := native_path_line_naturality Λ Y M N T e
  have hm := native_whisker_exchange_line Λ Y M N T e
  have hp := native_projection_line_naturality Λ Y M N T e
  run_tac do
    let stx ← `($(Lean.mkIdent `pretrace_functor_route)
      $(Lean.mkIdent `hK) $(Lean.mkIdent `hn) $(Lean.mkIdent `hm) $(Lean.mkIdent `hp))
    pretraceCheckedFinish stx

private theorem native_twist_projection_formula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    (A : DerivedCategory (Modules Λ X)) :
    twistProjectionMap Λ f LS LX e A =
      (tensorShiftIso Λ S LS ((moduleObjectDerivedPushforward Λ f).obj A)).inv ≫
        projectionMateMap Λ f A
          (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≫
        (moduleObjectDerivedPushforward Λ f).map
          ((A ◁ e.hom) ≫ (tensorShiftIso Λ X LX A).hom) := by
  unfold twistProjectionMap
  run_tac pretraceCongrGoal

private theorem native_inverse_prefix
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ Z : Scheme.{u}, Modules Λ Z)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y))
      e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))) :
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
    let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
    let H := twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
    let b := secondPretraceExchangeMap Λ Y M
    let tA := tensorShiftIso Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
      (F.obj (R.obj M))
    let w := tensorShiftIso Λ (diagonalSurface Y) (L (diagonalSurface Y)) (A.obj M)
    let r := projectionMateMap Λ (secondProjection Y) (A.obj M) T ≫
      U.map (A.obj M ◁ e.hom)
    let τ := twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e (A.obj M)
    letI : IsIso b := secondPretraceExchangeMap_isIso Λ Y M hb
    letI : IsIso τ := hp
    (U.map w.hom ≫ inv τ ≫ H.map (inv b)) ≫ tA.inv ≫
      ((b ▷ T) ≫ r) = 𝟙 _ := by
  let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let A := moduleObjectDerivedPullback Λ (firstProjection Y)
  let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
  let H := twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
  let b := secondPretraceExchangeMap Λ Y M
  let tA := tensorShiftIso Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
    (F.obj (R.obj M))
  let tB := tensorShiftIso Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
    (U.obj (A.obj M))
  let w := tensorShiftIso Λ (diagonalSurface Y) (L (diagonalSurface Y)) (A.obj M)
  let r := projectionMateMap Λ (secondProjection Y) (A.obj M) T ≫
    U.map (A.obj M ◁ e.hom)
  let τ := twistProjectionMap Λ (secondProjection Y)
    (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e (A.obj M)
  have : IsIso b := secondPretraceExchangeMap_isIso Λ Y M hb
  have : IsIso τ := hp
  have hn : (b ▷ T) ≫ tB.hom = tA.hom ≫ H.map b := by
    have hh := tensorShiftIso_naturality Λ (ProjectiveLine Y)
      (L (ProjectiveLine Y)) b
    simp only [tensorHom_id] at hh
    run_tac pretraceFinish (Lean.mkIdent `hh)
  have ht : τ = tB.inv ≫ r ≫ U.map w.hom := by
    have hf := native_twist_projection_formula Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e (A.obj M)
    run_tac do
      let stx ← `($(Lean.mkIdent `normalize_twist_formula) $(Lean.mkIdent `hf))
      pretraceCheckedFinish stx
  have hh : H.map (inv b) ≫ H.map b = 𝟙 _ := by
    run_tac do
      let stx ← `($(Lean.mkIdent `map_inverse_hom) $(Lean.mkIdent `H) $(Lean.mkIdent `b))
      pretraceCheckedFinish stx
  have hu : U.map w.hom ≫ U.map w.inv = 𝟙 _ := by
    run_tac do
      let stx ← `($(Lean.mkIdent `map_iso_hom_inv) $(Lean.mkIdent `U) $(Lean.mkIdent `w))
      pretraceCheckedFinish stx
  run_tac do
    let stx ← `($(Lean.mkIdent `cancel_plain_prefix)
      $(Lean.mkIdent `hn) $(Lean.mkIdent `ht)
      ($(Lean.mkIdent `tA)).inv_hom_id ($(Lean.mkIdent `tB)).hom_inv_id
      (IsIso.inv_hom_id $(Lean.mkIdent `τ)) $(Lean.mkIdent `hh) $(Lean.mkIdent `hu))
    pretraceCheckedFinish stx

private theorem native_first_trace_pretrace
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ Z : Scheme.{u}, Modules Λ Z)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (hq : IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y)
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)
      (((DerivedCategory.singleFunctor
        (Modules Λ (ProjectiveLine Y)) 0).obj
          (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y))
      e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
    (h₁ : IsIso (projectionMap Λ (firstProjection Y) M
      (((DerivedCategory.singleFunctor
        (Modules Λ (diagonalSurface Y)) 0).obj
          (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
    (t : d.R₁.R.obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ⟶
      unit Λ (ProjectiveLine Y)) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      (X := (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules Λ (diagonalSurface Y)) 0).obj
              (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
      ((moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules Λ (diagonalSurface Y)) 0).obj
              (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso Λ (diagonalSurface Y)
            (L (diagonalSurface Y))
            ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap Λ (secondProjection Y)
          (L (ProjectiveLine Y)) (L (diagonalSurface Y))
          e
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) hp ≫
        (twist Λ (ProjectiveLine Y)
          (L (ProjectiveLine Y))).map
          (by
            unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
            exact @inv _ _ _ _
              ((condensedAmbientExchange Λ (square Y)).app M) hb)) ≫
      counitProjectionPart Λ Y (L (ProjectiveLine Y))
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) hq ≫
      projectionMateMap Λ (ProjectiveLine Y ↘ Y) M
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
          (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
            (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ firstTraceExchange Λ Y
          (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
            (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
          (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) e) ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        ((M ◁ firstNativeFunctional Λ Y L d
          (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) t) ≫
          (M ◁ (singleUnitIso Λ (ProjectiveLine Y)).hom) ≫ (ρ_ M).hom) =
    firstTerminalFunctional Λ Y L d M
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) t h₁ := by
  let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
  let N := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
    (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧
  let q := projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T
  let π := projectionMap Λ (firstProjection Y) M N
  let v₀ := (M ◁ firstNativeFunctional Λ Y L d N t) ≫
    (M ◁ (singleUnitIso Λ (ProjectiveLine Y)).hom) ≫ (ρ_ M).hom
  have : IsIso q := hq
  have : IsIso π := h₁
  have hk := native_kunneth_line Λ Y M T N e
  have hi := native_inverse_prefix Λ Y L e M hb hp
  let A := moduleObjectDerivedPullback Λ (firstProjection Y)
  let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
  let b := secondPretraceExchangeMap Λ Y M
  let r := projectionMateMap Λ (secondProjection Y) (A.obj M) T ≫
    U.map (A.obj M ◁ e.hom)
  let y := (b ▷ T) ≫ r
  unfold firstTerminalFunctional counitProjectionPart
  refine cancel_functor_route (R := R) (q := q) (p := π) (y := y) ?_ ?_ v₀
  · run_tac pretraceExactRaw (Lean.mkIdent `hi)
  · run_tac pretraceExactRaw (Lean.mkIdent `hk)

/-- The trace-free Kunneth comparison, with the q projection cancelled.

Source: current blueprint, rational projective-line triangle proof, First identity;
the native tensor-square coherence and the categorical Kunneth factorization.
(blueprint: lem-sfb-rational-p1-first-trace-pretrace).

Proof: apply the two Kunneth factorizations to M and the shifted line T. The first
route is the q projection followed by exchange on M and the second projection.
The second is the right-factor q projection followed by the opposite exchange on
T and the first projection. Transport their equality by the conjugate path
comparison. Naturality in the fixed secondLineComparison identifies the second route with
firstTraceExchange. Expand twistProjectionMap and cancel the tensorShiftIso
pairs. Invertibility of the displayed exchange and projections permits cancelling
the first route and the first projection. The resulting equation is exactly the
one below after postcomposing with the direct image of the arbitrary functional
in the fixed first direct image, its single-unit comparison, and the right unitor.
Functoriality combines this suffix with the inverse first projection into
firstTerminalFunctional. Diagram supplies only the canonical first-direct-image
identification. No prescribed trace, diagonal class, or integration equation is used. -/
theorem first_trace_pretrace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (d : Diagram (coefficient l c).X Y (line l c))
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (hq : IsIso (projectionMap (coefficient l c).X (ProjectiveLine Y ↘ Y)
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
          (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M))
    (hp : IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)))
    (h₁ : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
    (t : d.R₁.R.obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ⟶
      unit (coefficient l c).X (ProjectiveLine Y)) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (X := (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
            (line l c (diagonalSurface Y))
            ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap (coefficient l c).X (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)) hp ≫
        (twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).map
          (by
            unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
            exact @inv _ _ _ _
              ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)) ≫
      counitProjectionPart (coefficient l c).X Y (line l c (ProjectiveLine Y))
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M) hq ≫
      projectionMateMap (coefficient l c).X (ProjectiveLine Y ↘ Y) M
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
            (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ firstTraceExchange (coefficient l c).X Y
          (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
            (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
          (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
            (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) (secondLineComparison l c k p hpl Y)) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        ((M ◁ firstNativeFunctional (coefficient l c).X Y (line l c) d
          (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) t) ≫
          (M ◁ (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom) ≫ (ρ_ M).hom) =
    firstTerminalFunctional (coefficient l c).X Y (line l c) d M
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) t h₁ := by
  have h := native_first_trace_pretrace (coefficient l c).X Y (line l c)
    (secondLineComparison l c k p hpl Y) d M
    (by run_tac pretraceExact (Lean.mkIdent `hq))
    (by run_tac pretraceExact (Lean.mkIdent `hb))
    (by run_tac pretraceExact (Lean.mkIdent `hp))
    (by run_tac pretraceExact (Lean.mkIdent `h₁)) t
  run_tac pretraceFinish (Lean.mkIdent `h)

end AlgebraicGeometry.ProEtale.RationalP1
