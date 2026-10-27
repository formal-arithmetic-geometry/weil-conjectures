## What changed

Updated `Sheaf.CategoryTheory.SignedKoszulBasisCoproduct` so the assigned recursive
coproduct theorem is proved by induction on the number of factors.  The induction
combines two named split-off statements in the same module: the one-factor base case
and the successor tensor/reindexing step.  The module's proof imports are unchanged.
The corresponding DAG node proof and proof dependencies now name the two split steps.

## Proved and sorry left

Closed the assigned sorry in `isColimit_ringedNegativeKoszulBasis_succ` by a real
induction.  Two strictly smaller proof obligations remain as named public theorems:

- `isColimit_ringedNegativeKoszulBasis_base`, node
  `lem-cbc-signed-koszul-basis-coproduct-base`;
- `isColimit_ringedNegativeKoszulBasis_step`, node
  `lem-cbc-signed-koszul-basis-coproduct-step`.

No definition contains a sorry.

## No longer needed

No imports or existing proof dependencies were removed.  The original direct
completion-model dependency is retained by both split steps.

## Where the brief, the DAG or earlier work was wrong

The original node presented the full induction as one proof obligation and had no
Lean declarations for its base and successor gluing steps.  The delivery records
those two strictly simpler intermediate statements so the main theorem's induction
is explicit and checkable.

## New nodes

`lem-cbc-signed-koszul-basis-coproduct-base` records the one-factor degreewise
coproduct, split by the supported degrees -1 and 0 and the zero degrees.

`lem-cbc-signed-koszul-basis-coproduct-step` records the successor induction step,
using the tail coproduct hypothesis, tensor preservation, and finite subset
reindexing.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
