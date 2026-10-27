## What changed

Removed the unused direct public import `Mathlib.CategoryTheory.Idempotents.Basic`
from `lean/Sheaf/SixFunctorsBasics/BrownHypotheses.lean`. The remaining imports
still provide every declaration used by the module and its public signatures.
The module compiles unchanged apart from this import pruning. The final
`brownHypotheses` theorem remains marked `STATEMENT-DISPUTED`, with its original
named `sorry`, because the unrestricted arbitrary-field compactness assertion is
not derivable from the stated hypotheses.

## Proved and sorry left

No original holes were closed and no holes were added. The one existing hole
remains in `CategoryTheory.brownHypotheses`, whose node is
`sk-lem-brown-hypotheses`. This theorem is explicitly disputed in its source
comment: arbitrary positive-characteristic fields do not provide the uniform
Ext bounds needed for the compactness clause. All other declarations in the item
remain proved.

## No longer needed

The direct public import `Mathlib.CategoryTheory.Idempotents.Basic` is no longer
needed. The module's use of `IsIdempotentComplete` is available through the
remaining imports, and `tools/import_prune_check.py` reports no downstream
consumer that relied on the removed re-export. No declaration, node, or unit
step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's final Brown assertion is explicitly disputed in the current module and
node. Its unrestricted compactness clause is false in general: the module's
existing counterexample notes use an infinite positive-characteristic field and
unbounded Kummer cohomology. The available finite-field compactness theorem
requires a `FiniteFieldDatum`, while the integral theorem requires an explicit
uniform Ext bound. Neither hypothesis is present in `brownHypotheses`, so no
sound proof of that theorem can be supplied without changing its statement.
The import pruning preserves the theorem and its signature exactly.

## New nodes

None.

## Forced adaptations

None. No other module was edited; static import-prune checking found no affected
consumer of the removed public import.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 3 OK, 1 SLOW.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.SixFunctorsBasics.BrownHypotheses": "9b5a8de302a619eeffc417d5815ee32bd063312c"}, "results": {"Sheaf.Paper.ExceptionalInverseImageExistence": {"hash": "e047ddc64ca96bb191cbf95acc82e09bbcecd38a", "status": "SLOW"}, "Sheaf.Paper.LocalizingExceptionalAdjoint": {"hash": "9b80929ae886e8305a73db59aae3e626c6c33cd3", "status": "OK"}, "Sheaf.SixFunctorsBasics.BrownHypothesesCoefficientIso": {"hash": "80cf11f0cc781fe2530a33ebe045d127e0d1bae7", "status": "OK"}, "Sheaf.SixFunctorsBasics.BrownHypothesesFiniteField": {"hash": "40b1ac159f94b5a3cd0b71c7acef53f076a729f5", "status": "OK"}}, "seconds": 181, "time": "2026-10-28T05:17:17+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
