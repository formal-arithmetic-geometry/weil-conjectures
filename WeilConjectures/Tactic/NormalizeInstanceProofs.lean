/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Elab.BuiltinNotation

/-!
# The tactic `normalize_instance_proofs`

`normalize_instance_proofs P at h₁ … hₙ ⊢`, for a proposition `P` which is a type class (such as
`Precoherent Profinite`), replaces every proof of `P` occurring in the types of the hypotheses
`hᵢ` and in the goal by the instance of `P` found by instance search.

Different elaborations of the same statement may carry different proofs of `P` (the instance
found by instance search, or an auxiliary proof constant reached by unification). They are
definitionally equal by proof irrelevance, but when they occur deep inside the implicit arguments
of large types, checking this definitional equality can make the unifier and the kernel unfold
the surrounding definitions and time out. After normalization, the proofs of `P` are
syntactically equal, so that hypotheses and goal can be combined as usual.

Each replacement casts along the motive `fun z ↦ T[c := z]` (`T` the type, `c` the proof
replaced) and the equation `c = r` given by `proof_irrel`, so that the kernel only checks
instances of the motive by `β`-reduction.
-/

public meta section

namespace NormalizeInstanceProofs

open Lean Meta Elab Tactic

/-- The proofs of `P` occurring in `e`, other than `r`: the closed subterms whose head constant
has a type with conclusion headed by the head constant of `P`, and whose type is `P`. -/
def proofsOf (P r e : Expr) : MetaM (Array Expr) := do
  let some cP := P.getAppFn.constName? | throwError "{P} is not an application of a constant"
  let acc ← IO.mkRef (#[] : Array Expr)
  forEachExpr e fun t ↦ do
    if t.hasLooseBVars || t == r then return
    let some c := t.getAppFn.constName? | return
    let some info := (← getEnv).find? c | return
    unless info.type.getForallBody.getAppFn.constName? == some cP do return
    if (← acc.get).contains t then return
    if (← inferType t) == P then acc.modify (·.push t)
  acc.get

/-- The motive `fun z ↦ T[c := z]` and the proof of `T = T[c := r]`, for proofs `c r : P`. -/
def castData (T P c r : Expr) : MetaM (Expr × Expr) := do
  let lvl ← getLevel T
  let motive ← withLocalDeclD `z P fun z ↦
    mkLambdaFVars #[z] (T.replace fun t ↦ if t == c then some z else none)
  let newT := motive.bindingBody!.instantiate1 r
  let eq := mkApp3 (mkConst ``proof_irrel) P c r
  return (newT, mkApp6 (mkConst ``congrArg [.zero, lvl.succ]) P (mkSort lvl) c r motive eq)

/-- Replace the proofs of `P` in the type of the hypothesis `h` by `r`. -/
def normalizeHyp (P r : Expr) (h : FVarId) : TacticM Unit := withMainContext do
  let mut T ← instantiateMVars (← h.getType)
  let mut val := mkFVar h
  for c in ← proofsOf P r T do
    let (newT, pf) ← castData T P c r
    val := mkApp4 (mkConst ``Eq.mp [← getLevel T]) T newT pf val
    T := newT
  if val == mkFVar h then return
  let g ← (← getMainGoal).assert (← h.getUserName) T val
  let g ← g.clear h
  let (_, g) ← g.intro1P
  replaceMainGoal [g]

/-- Replace the proofs of `P` in the goal by `r`. -/
def normalizeGoal (P r : Expr) : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  for c in ← proofsOf P r (← instantiateMVars (← g.getType)) do
    let T ← instantiateMVars (← g.getType)
    let (newT, pf) ← castData T P c r
    let g' ← mkFreshExprSyntheticOpaqueMVar newT
    g.assign (mkApp4 (mkConst ``Eq.mpr [← getLevel T]) T newT pf g')
    g := g'.mvarId!
  replaceMainGoal [g]

/-- `normalize_instance_proofs P at h₁ … hₙ ⊢` replaces every proof of the type class
proposition `P` in the hypotheses `hᵢ` and the goal by the instance found by instance search. -/
elab "normalize_instance_proofs " P:term loc:(ppSpace Lean.Parser.Tactic.location)? : tactic => do
  let (P, r) ← withMainContext do
    let P ← instantiateMVars (← Term.elabType P)
    let r ← synthInstance P
    return (P, r)
  withLocation (expandOptLocation (mkOptionalNode loc))
    (fun h ↦ normalizeHyp P r h) (normalizeGoal P r)
    (fun _ ↦ throwError "normalize_instance_proofs failed")

end NormalizeInstanceProofs
