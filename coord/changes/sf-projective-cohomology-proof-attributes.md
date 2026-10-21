# WeilConjectures.sfSplitRings

## Reason

The expanded coefficient-ring abbreviation caused repeated typeclass and definitional
comparison work throughout the new proofs. The first complete proof compiled in
43.6 seconds, but a later delivery hit the 60-second file limit. Profiling a further
standalone compile showed 54.1 seconds, with substantial elaboration and linting cost.
Replacing `abbrev` by `def` with the identical type and body reduces compilation to
9.0 seconds. Removing all temporary profiling, the heartbeat increase, and the public
definition attributes gives a clean 6.3-second compile under the default heartbeat
budget. This is the definition-performance repair required by the worker brief;
the server time limit remains unchanged. No mathematical data or theorem statement
changes. The resulting object is definitionally equal to the original.

The earlier delivery preflight also requested a change record for local proof commands.
The public-definition reducibility attributes and increased heartbeat budget used during
development have now been removed. Only a local irreducibility attribute on the new
private explicit assembly definition remains. Its proved cell equation supplies its API.

## Old

```lean
abbrev sfSplitRings : Sheaf (Scheme.ProEt.topology U) RingCat.{max (u + 1) v} :=
  (sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj C
```

## New

```lean
def sfSplitRings : Sheaf (Scheme.ProEt.topology U) RingCat.{max (u + 1) v} :=
  (sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj C
```

The body is byte-identical. Only eager reducibility changes to ordinary definition
reducibility. The definition is still exposed and computable by unfolding it, with
exactly the same universes and parameters. All existing public definition bodies,
theorem signatures, visibility, and public imports otherwise remain unchanged.

Additional `omit ... in` commands apply only to new private helper declarations.
The bounded-above chain-representatives theorem is moved earlier so the main proof can
use it, retaining its original signature.

## Users

`tools/downstream.py Sheaf.Paper.ProjectiveCohomologySplitModel --uses sfSplitRings`
reports zero downstream modules and only the item itself as a textual user. A textual
search of `lean/Sheaf`, `lean/WeilConjectures`, and `quarantine` finds no external Lean
consumer of the name or import of the item module. All declarations of the item compile
with the new ordinary definition. No external consumer requires adaptation.
The node's parent dependencies and unit route are retained; nothing is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectiveCohomologySplitModel | K8 | Same coefficient object with ordinary reducibility; three proofs completed and private helpers added. |

No target statement changes. The coefficient object's mathematical meaning is identical,
so there is no semantic statement change to propagate or target hypothesis to review.

## Status

landed 20261021T183346-L-1606733 2026-10-21 (merge of deliver/K8/Sheaf.Paper.ProjectiveCohomologySplitModel)
