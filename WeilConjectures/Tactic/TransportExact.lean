/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Tactic.FirstOrderApply

/-!

# Closing a goal by a definitionally equal hypothesis, kernel-friendly

`transport_exact h` closes the goal by `h` when the type of `h` and the goal are definitionally
equal but spelled differently (for instance objects of a full subcategory against their ambient
forms, inside large composites of derived functors). The kernel may unfold such large terms in
the wrong order and run out of heartbeats on `exact h`, even though each pair of differing
subterms is definitionally equal in milliseconds.

As in `Mathlib.Tactic.FirstOrderApply.transport`, `h` is transported along a congruence proof of
`HEq A B` built along the common structure of its type `A` and the goal `B`, whose leaves are
closed by `HEq.refl` and are small; the proof is then added as an auxiliary theorem
(`Mathlib.Tactic.FirstOrderApply.sealProof`). The difference is in the descent: two applications
with the same head are compared argument by argument as soon as each pair of explicit arguments
is plausibly equal (`Mathlib.Tactic.FirstOrderApply.plausibleEq`) *or* definitionally equal
within a small heartbeat budget. This keeps the leaves small when an explicit argument is an
object spelled in two ways (e.g. `α.app E` against `α.app E'`), where `HEq.refl` on the whole
application would make the kernel unfold `α`.

-/

public meta section

open Lean Meta Elab Tactic Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.TransportExact

/-- `transport_exact h` closes the goal by `h`, whose type is definitionally equal to the goal,
along a congruence proof with small leaves, added as an auxiliary theorem. -/
elab "transport_exact " h:term : tactic => withMainContext do
  let g ← getMainGoal
  let a ← elabTerm h none
  let A ← instantiateMVars (← inferType a)
  let B ← instantiateMVars (← g.getType)
  let pf ← if A == B then pure a else do
    let e ← heqProof (← IO.mkRef {}) A B
    pure (mkApp4 (mkConst ``Eq.mp [.zero]) A B
      (mkApp4 (mkConst ``eq_of_heq [1]) (mkSort 0) A B e) a)
  let pf ← instantiateMVars pf
  if pf.hasExprMVar then throwError "transport_exact: the proof has unassigned metavariables"
  g.assign (← sealProof B pf)
  replaceMainGoal []

/-- `transport_rfl` closes a goal `l = r` with `l` and `r` definitionally equal but spelled
differently, along a congruence proof with small leaves, added as an auxiliary theorem. -/
elab "transport_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let B ← instantiateMVars (← g.getType)
  let some (α, l, r) := (← whnfR B).eq? | throwError "transport_rfl: the goal is not an equation"
  let e ← heqProof (← IO.mkRef {}) l r
  let u ← getLevel α
  let pf ← instantiateMVars (mkApp4 (mkConst ``eq_of_heq [u]) α l r e)
  g.assign (← sealProof B pf)
  replaceMainGoal []

end Mathlib.Tactic.TransportExact
