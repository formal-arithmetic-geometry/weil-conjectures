/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso

/-!

# Tactics for gluing identities between large concrete composites

The identities of the specialization of the class of a component
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specializesComponentClass_deformation`)
compose lemmas whose statements are huge composites of six-functor maps on bounded constructible
complexes. Their statements agree up to proof arguments and to unfolding of reducible
definitions, but the elaborator's unifier compares the proof arguments through proof
irrelevance, which infers the types of very large proof terms and takes minutes or more. The
tactics of this file avoid the unifier and leave the identifications to the kernel:

* `instantiate_by_match c [x := e, …] as h` instantiates a lemma `c`, matching the types of the
  given arguments against the binder types of `c` syntactically (`synMatch`: metavariables are
  assigned directly, proof arguments are skipped, reducible definitions and `(F ⋙ G).obj` are
  unfolded on demand);
* `glue_unit_class h h'` closes a goal `c ≫ L(s') ≫ ?φ ≫ ν = Z` from
  `h : c ≫ L(s ≫ q) ≫ r = w ≫ v` and `h' : w ≫ v ≫ ν = Z`
  (`CategoryTheory.comp_map_comp_comp_eq_of_eq`);
* `trans_kernel_last h₁ k` reduces a goal `a = d` to `b = c` for `h₁ : a = b` and
  `k T' e : c = d`, where `e : _ ⟶ T'` is the last factor of `d`;
* `close_by_match_lhs c` closes a goal `l = eqToHom r` with a lemma `c : … → l' = eqToHom r'`
  whose left-hand side is matched syntactically against `l`.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- Gluing an identity `c ≫ L(s ≫ q) ≫ r = w ≫ v` to `w ≫ v ≫ ν = Z`: the composite
`c ≫ L(s') ≫ (L(q) ≫ r) ≫ ν` is `Z` for any `s'` equal to `s`. -/
lemma comp_map_comp_comp_eq_of_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {L : 𝒞 ⥤ 𝒟}
    {u A₁ A₂ B₀ : 𝒟} {U₁ U₂ U₃ : 𝒞} (c : u ⟶ L.obj U₁) (s s' : U₁ ⟶ U₂) (q : U₂ ⟶ U₃)
    (r : L.obj U₃ ⟶ A₁) (w : u ⟶ A₂) (v : A₂ ⟶ A₁) (ν : A₁ ⟶ B₀) (Z : u ⟶ B₀) (hs : s' = s)
    (h : c ≫ L.map (s ≫ q) ≫ r = w ≫ v) (h' : w ≫ v ≫ ν = Z) :
    c ≫ L.map s' ≫ (L.map q ≫ r) ≫ ν = Z := by
  subst hs; rw [← h', ← reassoc_of% h, L.map_comp]; simp only [Category.assoc]

/-- `e.hom ≫ e.inv ≫ H(eqToHom h) = 𝟙` for a natural isomorphism `e : G ⋙ H ≅ F`. -/
lemma NatIso.hom_app_comp_inv_app_comp_map_eqToHom {C D E : Type*} [Category C] [Category D]
    [Category E] {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (e : G ⋙ H ≅ F) (X : C)
    (h : G.obj X = G.obj X) : e.hom.app X ≫ e.inv.app X ≫ H.map (eqToHom h) = 𝟙 _ := by
  simp

/-- `e.hom ≫ e.inv ≫ H(eqToHom h) = H(eqToHom h')` for a natural isomorphism `e : G ⋙ H ≅ F`. -/
lemma NatIso.hom_app_comp_inv_app_comp_map_eqToHom_eq {C D E : Type*} [Category C]
    [Category D] [Category E] {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (e : G ⋙ H ≅ F) (X : C)
    {Y : D} (h h' : G.obj X = Y) :
    e.hom.app X ≫ e.inv.app X ≫ H.map (eqToHom h) = H.map (eqToHom h') := by
  simp

end CategoryTheory

/-- The two sides of an equation. -/
meta def eqSidesOf (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let e ← Lean.Meta.whnfR (← Lean.instantiateMVars e)
  let some (_, l, r) := e.eq? | throwError "not an equation"
  return (l, r)

/-- The two factors of a composite `f ≫ g`. -/
meta def compFactors (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let e := e.consumeMData
  unless e.isAppOfArity ``CategoryStruct.comp 7 do throwError "not a composite"
  return (e.getArg! 5, e.getArg! 6)

/-- `glue_unit_class h h'` closes a goal `c ≫ L(s') ≫ ?φ ≫ ν = Z` from
`h : c ≫ L(s ≫ q) ≫ r = w ≫ v` and `h' : w ≫ v ≫ ν = Z`, where `s'` and `s` are definitionally
equal: it assigns `?φ := L(q) ≫ r` and closes the goal with `comp_map_comp_comp_eq_of_eq`. The
identifications `s' = s` and of the remaining terms (which agree up to their proof arguments) are
left to the kernel: the elaborator, through proof irrelevance, infers the types of large proof terms
and needs minutes for them. -/
elab "glue_unit_class " h:ident h':ident : tactic => Lean.Elab.Tactic.withMainContext do
  let he ← Lean.Elab.Tactic.elabTerm h none
  let he' ← Lean.Elab.Tactic.elabTerm h' none
  let (l, wv) ← eqSidesOf (← Lean.Meta.inferType he)
  let (l', Z) ← eqSidesOf (← Lean.Meta.inferType he')
  let (c, rest) ← compFactors l
  let (m, r) ← compFactors rest
  let (s, q) ← compFactors m.consumeMData.appArg!
  let (w, v) ← compFactors wv
  let (_, restD) ← compFactors l'
  let (_, ν) ← compFactors restD
  let (lG, _) ← eqSidesOf (← Lean.Elab.Tactic.getMainTarget)
  let (_, restG) ← compFactors lG
  let (mG, restG') ← compFactors restG
  let (φG, _) ← compFactors restG'
  let s' := mG.consumeMData.appArg!
  -- `?φ := L(q) ≫ r`, with `L(q)` obtained from `L(s ≫ q)` by changing the morphism
  let m := m.consumeMData
  let some (_, _, X, Y) := (← Lean.Meta.whnfR (← Lean.Meta.inferType q)).app4? ``Quiver.Hom
    | throwError "unexpected type"
  let margs := m.getAppArgs
  let n := margs.size
  let mq := Lean.mkAppN m.getAppFn (((margs.set! (n - 3) X).set! (n - 2) Y).set! (n - 1) q)
  let some (_, _, A, _) := (← Lean.Meta.whnfR (← Lean.Meta.inferType mq)).app4? ``Quiver.Hom
    | throwError "unexpected type"
  let rest := rest.consumeMData
  let φ := Lean.mkAppN rest.getAppFn ((rest.getAppArgs.set! 2 A).set! 5 mq)
  unless φG.consumeMData.isMVar do throwError "the middle factor is not a metavariable"
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType φG) (← Lean.Meta.inferType φ) do
    throwError "the middle factor has the wrong type"
  φG.consumeMData.mvarId!.assign φ
  let hs ← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl s) (← Lean.Meta.mkEq s' s)
  let pf ← Lean.Meta.mkAppM ``CategoryTheory.comp_map_comp_comp_eq_of_eq
    #[c, s, s', q, r, w, v, ν, Z, hs, he, he']
  let some (_, _, U₁, U₂) := (← Lean.Meta.whnfR (← Lean.Meta.inferType s')).app4? ``Quiver.Hom
    | throwError "unexpected type"
  let args := pf.getAppArgs
  -- the objects of `s'`, so that the statement of the proof is the goal up to proof arguments
  (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkAppN pf.getAppFn ((args.set! 9 U₁).set! 10 U₂))
  Lean.Elab.Tactic.replaceMainGoal []


section SynMatch
open Lean Meta
mutual
/-- Syntactic first-order matching of a pattern `p` (with metavariables) against a term `t`,
reporting the path to the first conflict. -/
meta partial def synMatch (p t : Expr) : MetaM Unit := do
  try synMatchCore p t
  catch e =>
    let p' ← instantiateMVars p
    throwError m!"{e.toMessageData}\n<- {p'.getAppFn} /{p'.getAppNumArgs}"

/-- The matching step of `synMatch`: metavariables of `p` are assigned without type check,
proof arguments are skipped, `(F ⋙ G).obj X` is unfolded one step, `ι.obj m` and `ι.map f` for the
inclusion `ι` of a full subcategory are matched against projections, reducible definitions are
unfolded, and the unifier is the last resort. -/
meta partial def synMatchCore (p t : Expr) : MetaM Unit := do
  let p ← instantiateMVars p
  if p == t then return
  let p' := p.consumeMData; let t' := t.consumeMData
  if let .mvar m := p' then
    unless ← m.isAssigned do
      m.assign t'
      return
  -- `(F ⋙ G).obj X` and `(F ⋙ G).map f` are `G.obj (F.obj X)` and `G.map (F.map f)`
  let compUnfold (e : Expr) : MetaM (Option Expr) := do
    if e.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
        e.isAppOfArity ``CategoryTheory.Functor.map 8 then
      -- the functor, with reducible definitions (`abbrev`s of composites) unfolded
      let FG ← whnfR (e.getArg! 4)
      -- `(𝟭 C).obj X` and `(𝟭 C).map f` are `X` and `f`
      if FG.isAppOf ``Functor.id then return some e.appArg!
      unless FG.isAppOf ``Functor.comp do return none
      let some FG' ← unfoldDefinition? FG | return none
      let e' := mkAppN e.getAppFn (e.getAppArgs.set! 4 FG')
      let some e2 ← unfoldDefinition? e' | return none
      let r ← whnfCore e2
      return some r
    return none
  if let some p2 ← compUnfold p' then return ← synMatchCore p2 t'
  if let some t2 ← compUnfold t' then return ← synMatchCore p' t2
  -- `ι.obj m` against a projection `Y.obj`, and `ι.map f` against a projection `g.hom`
  if p'.isApp && ((p'.getAppFn.isProj &&
      (p'.getAppFn.find? (·.isAppOf ``ObjectProperty.ι)).isSome) ||
      ((p'.isAppOf ``Prefunctor.obj || p'.isAppOf ``Prefunctor.map) &&
        ((p'.getArg! 4).find? (·.isAppOf ``ObjectProperty.ι)).isSome)) then
    do
      let arg := p'.appArg!
      let tStruct? : Option Expr ← do
        match t' with
        | .proj _ _ e => pure (some e)
        | _ =>
          if let some n := t'.getAppFn.constName? then
            if (← getProjectionFnInfo? n).isSome then pure (some t'.appArg!) else pure none
          else pure none
      if let some e := tStruct? then
        return ← synMatch arg e
  match p', t' with
  | .sort u, .sort v => discard <| isLevelDefEq u v
  | .const n us, .const n' vs =>
    if n == n' && us.length == vs.length then
      for (u, v) in us.zip vs do discard <| isLevelDefEq u v
      return
    throwError m!"synMatch: constants {p'} vs {t'}"
  | .forallE _ d b _, .forallE _ d' b' _ => synMatch d d'; synMatch b b'
  | .lam _ d b _, .lam _ d' b' _ => synMatch d d'; synMatch b b'
  | .proj s i e, .proj s' i' e' =>
    if s == s' && i == i' then synMatch e e' else throwError m!"synMatch: projections"
  | .proj s i e, _ =>
    if let some n := t'.getAppFn.constName? then
      if let some info ← getProjectionFnInfo? n then
        -- the projection must be the same field of the same structure
        if info.i == i && t'.getAppNumArgs == info.numParams + 1 &&
            info.ctorName.getPrefix == s then
          return ← synMatch e t'.appArg!
    let t2 ← whnfR t'
    if t2 != t' then return ← synMatch p' t2
    if ← isDefEq p' t' then return
    throwError m!"synMatch conflict (proj):\n{p'}\nvs\n{t'}"
  | _, _ =>
    if p'.isApp && t'.isApp && p'.getAppNumArgs == t'.getAppNumArgs then
      let fp := p'.getAppFn; let ft := t'.getAppFn
      let ok ← (do synMatch fp ft; pure true) <|> pure false
      if ok then
        let ps := p'.getAppArgs; let ts := t'.getAppArgs
        for i in [0:ps.size] do
          if ← (do try isProof ts[i]! catch _ => pure false) then
            let pi ← instantiateMVars ps[i]!
            if let .mvar m := pi.consumeMData then
              unless ← m.isAssigned do m.assign ts[i]!
            continue
          synMatch ps[i]! ts[i]!
        return
    let p2 ← whnfR p'
    if p2 != p' then return ← synMatch p2 t'
    let t2 ← whnfR t'
    if t2 != t' then return ← synMatch p' t2
    -- one delta step (cheaper than `whnf`, which may compute projections), on the side whose
    -- head has the larger definitional height first, as in the kernel
    let height (e : Expr) : MetaM Nat := do
      let some n := e.getAppFn.constName? | return 0
      match (← getEnv).find? n with
      | some (.defnInfo d) => return match d.hints with | .regular h => h.toNat + 1 | _ => 0
      | _ => return 0
    let tFirst := (← height t') > (← height p')
    for side in (if tFirst then [true, false] else [false, true]) do
      if side then
        if let some t4 ← unfoldDefinition? t' then
          let s ← saveState
          try synMatch p' t4; return catch _ => s.restore
      else
        if let some p4 ← unfoldDefinition? p' then
          let s ← saveState
          try synMatch p4 t'; return catch _ => s.restore
    let p3 ← whnf p'
    if p3 != p' then
      if ← (do synMatch p3 t'; pure true) <|> pure false then return
    if ← isDefEq p' t' then return
    throwError m!"synMatch conflict:\n{p'}\nvs\n{t'}"

end
end SynMatch

open Lean Meta Elab Tactic in
/-- `instantiate_by_match c [x := e, …] as h`: instantiate the lemma `c`, matching the types of
the given arguments syntactically (`synMatch`), and add the result as `h`. -/
elab "instantiate_by_match " c:ident " [" args:(ident ":=" term),* "] " "as " h:ident : tactic =>
  withMainContext do
  let cst ← realizeGlobalConstNoOverload c
  let e ← mkConstWithFreshMVarLevels cst
  let ty ← inferType e
  let mut names : Array Name := #[]
  let mut t := ty
  while t.isForall do
    names := names.push t.bindingName!
    t := t.bindingBody!
  let (mvs, _, concl) ← forallMetaTelescope ty
  for a in args.getElems do
    let nm := a.raw[0].getId
    let some idx := names.findIdx? (· == nm) | throwError m!"no binder {nm}"
    let ety ← instantiateMVars (← inferType mvs[idx]!)
    let v ← elabTerm a.raw[2] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    synMatch ety (← inferType v)
    (mvs[idx]!).mvarId!.assign v
  let pf ← instantiateMVars (mkAppN e mvs)
  let concl ← instantiateMVars concl
  if pf.hasExprMVar then
    let mut un : Array Name := #[]
    for i in [0:mvs.size] do
      unless ← mvs[i]!.mvarId!.isAssigned do un := un.push names[i]!
    throwError m!"unassigned arguments remain: {un}"
  let g ← getMainGoal
  let (_, g') ← (← g.assert h.getId concl pf).intro1P
  replaceMainGoal [g']

/-- `trans_kernel_last h₁ k` is `trans_kernel h₁ (k T' e)`, where `e : _ ⟶ T'` is the last factor
of the right-hand side of the goal. -/
elab "trans_kernel_last " h₁:term:max k:term:max : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let e₁ ← Lean.Elab.Tactic.elabTerm h₁ none
  let ek ← Lean.Elab.Tactic.elabTerm k none
  let some (_, _, rhs) := (← Lean.Meta.whnfR (← g.getType)).eq? | throwError "goal"
  let mut last := rhs
  while last.isAppOfArity ``CategoryStruct.comp 7 do
    last := last.getArg! 6
  let some (_, _, _, T') := (← Lean.Meta.whnfR (← Lean.Meta.inferType last)).app4? ``Quiver.Hom
    | throwError "last factor"
  let e₂ := Lean.mkApp2 ek T' last
  let some (α, a, b) := (← Lean.Meta.whnfR (← Lean.Meta.inferType e₁)).eq? | throwError "h₁"
  let some (_, c, d) := (← Lean.Meta.whnfR (← Lean.Meta.inferType e₂)).eq? | throwError "k"
  let u ← Lean.Meta.getLevel α
  let mid ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
    (Lean.mkApp3 (Lean.mkConst ``Eq [u]) α b c)
  let p₁ := Lean.mkApp6 (Lean.mkConst ``Eq.trans [u]) α a b c e₁ mid
  let p := Lean.mkApp6 (Lean.mkConst ``Eq.trans [u]) α a c d p₁ e₂
  g.assign (← Lean.Meta.mkExpectedTypeHint p (← g.getType))
  Lean.Elab.Tactic.replaceMainGoal [mid.mvarId!]

open Lean Meta Elab Tactic in
/-- `close_by_match_lhs c` closes a goal `l = eqToHom r` with the lemma `c : … → l' = eqToHom r'`
(last argument `r'`), matching `l'` syntactically against `l` and taking `r' := r`; the comparison
is left to the kernel. -/
elab "close_by_match_lhs " c:ident : tactic => withMainContext do
  let g ← getMainGoal
  let cst ← realizeGlobalConstNoOverload c
  let e ← mkConstWithFreshMVarLevels cst
  let (mvs, _, concl) ← forallMetaTelescope (← inferType e)
  let tgt ← instantiateMVars (← g.getType)
  let some (_, l, rhs) := (← whnfR tgt).eq? | throwError "not an equation"
  let some (_, l', _) := (← whnfR concl).eq? | throwError "not an equation"
  synMatch l' l
  (mvs[mvs.size - 1]!).mvarId!.assign rhs.consumeMData.appArg!
  let pf ← instantiateMVars (mkAppN e mvs)
  if pf.hasExprMVar then throwError "close_by_match_lhs: unassigned arguments"
  g.assign (← mkExpectedTypeHint pf tgt)
  replaceMainGoal []

