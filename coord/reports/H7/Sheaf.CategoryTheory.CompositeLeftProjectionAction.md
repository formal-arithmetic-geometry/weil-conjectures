## What changed

Filled `CategoryTheory.compositeLeftProjectionAction_coherence` in
`Sheaf.CategoryTheory.CompositeLeftProjectionAction` directly from its six action axioms.
Joint naturality uses `hv` followed by `ht`. The unit calculation uses naturality at
`f.εIso.inv`, then `hv_unit` and `ht_unit`. The associativity calculation uses naturality
at `(f.μIso B B').inv`, then `hv_assoc`, `ht_assoc`, and naturality of `t` at
`v (F.obj B') M`. Functoriality and tensor bifunctoriality supply the reassociations.
This implements the existing seven-step node plan without changing any signature,
definition, public import, or dependency.

## Proved and sorry left

Closed the sole original hole, `CategoryTheory.compositeLeftProjectionAction_coherence`
(node `lem-pur-composite-left-projection-action`). One hole closed, zero holes added,
zero holes remaining, and no split-off statements.

Validation: `lcompile.py` accepted the complete module in 3.0 seconds with no
compiler diagnostics. The declaration signatures, definition and imports are unchanged;
every Lean line is at most 100 characters.

## No longer needed

None. Both declared dependencies, `def-sfb-monoidal-category` and
`def-sfb-strong-monoidal-functor`, are Mathlib leaves supplied by the existing
`Mathlib.CategoryTheory.Monoidal.Functor` import. No imports, nodes, or modules are pruned.
No extra imports are needed.

## Where the brief, the DAG or earlier work was wrong

None. The proof follows the existing node plan and preserves the unit route.
LeanFinder returned linear-functor coherence facts for a single acting category;
these do not directly provide this relative action-pasting theorem. Loogle and the
local Mathlib search supplied the elementary functor and tensor laws used here.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
