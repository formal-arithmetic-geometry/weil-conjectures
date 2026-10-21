## What changed

The item module now decomposes the ordinary pullback evaluation comparison into two named
intermediate theorems, `moduleEvalG_exists` and `moduleEvalG_unique`, and combines them in a
complete proof of `moduleEvalG_existsUnique`. The two intermediate theorem proofs remain
`sorry` and are recorded as new DAG nodes.

## Proved and sorry left

Closed: `moduleEvalG_existsUnique` (one public hole).

Added and left: `moduleEvalG_exists` and `moduleEvalG_unique` (two public split obligations),
with nodes `lem-sp-varying-ring-module-eval-g-existence` and
`lem-sp-varying-ring-module-eval-g-uniqueness`.

The existing public holes `extension_exact`, `evalPMate_isIso`, and `evalJInv_isIso` remain.

## No longer needed

None. The existing proof imports remain in use, and no DAG dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The retained attempt stated the ordinary comparison as one large obligation but supplied no
Lean declaration for its existence or uniqueness subarguments. The target can be reduced to
these two strictly smaller categorical results; the combination proof is now complete.

## New nodes

`lem-sp-varying-ring-module-eval-g-existence`: existence of the unit-normalized ordinary
pullback evaluation comparison.

`lem-sp-varying-ring-module-eval-g-uniqueness`: uniqueness of that comparison from its unit
equation.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
