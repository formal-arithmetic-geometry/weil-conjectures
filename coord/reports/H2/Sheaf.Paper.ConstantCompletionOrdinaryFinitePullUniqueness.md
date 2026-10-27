## What changed

Proved `CategoryTheory.ConstantCompletion.ordinaryFinitePull_unique` without changing
its statement. Apply the sheafified extension/restriction adjunction twice to each
component, identify the units with the actual insertion maps, cancel the
module-underlying isomorphism, and use the two normalization equations.
Added proved private helpers for these unit and Hom-equivalence formulas.
The proof uses `Sheaf.Paper.RingedTopoiTensorSections` directly and the DAG records
that dependency.

## Proved and sorry left

Closed the sole hole, `CategoryTheory.ConstantCompletion.ordinaryFinitePull_unique`
(node `lem-weil-pbc-constant-completion-ordinary-finite-pull-uniqueness`).
Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: 0.
No split-off statements or new modules. The complete proof compiled in 7.5 seconds;
the final packet also retains the existing adjunction and finite-limit binders
explicitly to avoid unused-section-variable warnings without changing the signature.

## No longer needed

Removed the proof import `Sheaf.Paper.ConstantCompletionOrdinaryFinitePullExistence`:
uniqueness uses only the adjunction units and does not require existence of the
comparison. That existence module remains needed by the parent existence-and-uniqueness
assembly; no whole module is withdrawn.
Removed `lem-weil-pbc-constant-completion-equivalence` from this node's proof dependencies:
its definitions remain statement dependencies, but its completion theorem is not used
in the uniqueness proof. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous proof step pointed back to the broad completion-equivalence node and
called for tensor-generator extensionality without naming its precise API. The
existing scalar-extension adjunction supplies that extensionality directly, twice,
so no further decomposition is necessary. The argument needs no Noetherian,
nonzero-ring, nontrivial-ideal, or positive-level assumption.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryFinitePullUniqueness": "48aca5f66cc32660270ccfe171a811dc69e98811"}, "results": {"Sheaf.Paper.ConstantCompletionOrdinaryFinitePull": {"hash": "1511cf7191ee512b808f4ce277ad3a94901698a9", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T04:04:55+0800", "transitive": 0, "version": 1}
```

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
