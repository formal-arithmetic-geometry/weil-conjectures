/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Tactic.Basic

/-!

# First-order instantiation of lemmas

`fo_have h := lemma using a₁, …, aₙ` and `fo_apply lemma using a₁, …, aₙ` instantiate the
implicit arguments of `lemma` by *first-order matching* of the types of its explicit hypotheses
against the types of the given terms `aᵢ` (and, for `fo_apply`, of its conclusion against the
goal), instead of by unification.

On large terms (for instance composites of derived functors), the unifier may unfold definitions
as soon as two subterms are not syntactically equal, even when they only differ by proofs or by
the instance path of an instance, and then run out of heartbeats. First-order matching assigns a
metavariable of the pattern directly to the corresponding subterm, compares applications with
the same head argument by argument, accepts any two proofs (proof irrelevance), and only falls
back to `isDefEq` on the smallest subterms where the two sides differ. Explicit arguments
are matched before implicit ones; an implicit argument which does not match yet is retried once
the others are matched.

The kernel then still has to identify the types of the given proofs with the instantiated
hypotheses, which may again unfold large definitions. So the given proofs (and, for `fo_apply`,
the conclusion) are transported along congruence proofs of `HEq A B` built along the common
structure of `A` and `B` (`heqProofAux`), whose leaves are small; arguments `rfl` and `HEq.rfl`
are proved the same way. Finally, a proof without remaining goals is added as an auxiliary
theorem (`sealProof`), so that the kernel checks it on its own.

-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.FirstOrderApply

/-- The equations `h : α = β` inside a pattern `cast h x` met by `foMatch` against a term which is
not a cast (assigned at the end of `foInstantiate`, by congruence). -/
initialize castEqs : IO.Ref (Array (MVarId × Expr × Expr)) ← IO.mkRef #[]

/-- `fo_have h := lemma using a₁, …, aₙ` adds `h : (the conclusion of lemma)`, where the
explicit hypotheses of `lemma` are the `aᵢ` (`_` for a hypothesis left as a new goal) and the
implicit arguments are found by first-order matching of the types. -/
elab "fo_have " h:ident " := " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let fe ← elabLemma f
    let (pf, newGoals) ← foInstantiate fe args.getElems none
    let ty ← instantiateMVars (← inferType pf)
    let pf ← instantiateMVars pf
    let pf ← if newGoals.isEmpty && !pf.hasMVar then sealProof ty pf else pure pf
    let g' ← (← getMainGoal).assert h.getId ty pf
    let (_, g'') ← g'.intro1P
    replaceMainGoal (g'' :: newGoals.toList)

/-- `fo_apply lemma using a₁, …, aₙ` closes the goal by `lemma`, matching its conclusion against
the goal and its explicit hypotheses against the `aᵢ` first-order (`_` for a hypothesis left as
a new goal). -/
elab "fo_apply " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let g ← getMainGoal
    let fe ← elabLemma f
    let (pf, newGoals) ← foInstantiate fe args.getElems (some (← instantiateMVars (← g.getType)))
    let pf ← instantiateMVars pf
    let pf ← if newGoals.isEmpty && !pf.hasMVar then
      sealProof (← instantiateMVars (← g.getType)) pf else pure pf
    g.assign pf
    replaceMainGoal newGoals.toList

end Mathlib.Tactic.FirstOrderApply
