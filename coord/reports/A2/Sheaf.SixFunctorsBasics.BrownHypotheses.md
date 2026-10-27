## What changed

Preserved the assigned `Sheaf.SixFunctorsBasics.BrownHypotheses` module and its
existing proved Brown criteria and obstruction lemmas. The disputed theorem
`CategoryTheory.brownHypotheses` remains unchanged with its named `sorry`, because
its arbitrary positive-characteristic compactness assertion is not derivable from
its hypotheses and is explicitly marked `STATEMENT-DISPUTED` in the current source
and DAG. Removed two redundant proof imports whose declarations remain available
transitively; the module compiles unchanged after this pruning.

## Proved and sorry left

No original hole was closed and no new hole was added. The sole remaining hole is
`CategoryTheory.brownHypotheses` (node `sk-lem-brown-hypotheses`). All other
existing declarations in the module remain complete. The delivered file compiles
with exactly this one `sorry`.

## No longer needed

Removed the direct import `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
Its declarations are supplied through the remaining imports, as verified by the
successful single-file compile. The direct `Sheaf.Paper.IntegralConstructibleCompactness`
import remains required by the conditional integral compactness theorem.
No DAG node or module is withdrawn, and no existing declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The current DAG and prior reviews correctly mark `CategoryTheory.brownHypotheses`
as disputed: finite-field compactness requires a finite-field datum, while the
integral compactness route requires an explicit uniform Ext bound. The theorem's
arbitrary-field hypotheses provide neither, so replacing its `sorry` with an
unsupported compactness argument would be unsound. This delivery keeps the exact
statement and records the valid partial result and import pruning.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.SixFunctorsBasics.BrownHypotheses": "bd9d357361da5ed07bc47faa19745e3c32050a0c"}, "own_failed": ["Sheaf.SixFunctorsBasics.BrownHypotheses"], "results": {}, "time": "2026-10-27T23:38:29+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
