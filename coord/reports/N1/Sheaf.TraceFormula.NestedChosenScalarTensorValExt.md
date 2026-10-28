## What changed

Proved `WeilConjectures.nestedChosenScalarTensor_val_ext` in
`Sheaf.TraceFormula.NestedChosenScalarTensorValExt`, with its statement unchanged.
The proof instantiates the existing normalized ordinary scalar-extension adjunction
for both coefficient maps. Injectivity of the two Hom equivalences reduces the
equality to nested tensor sections with coefficients 1 and 1. A private proved
helper identifies the adjunction unit with the chosen completed tensor section.

Added proof-only imports of
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction` and
`import all Sheaf.Paper.FiniteFreeCompletedScalarComparison` (the latter supplies
its private object/map equations). No public interface or other existing module
changed. Updated the item's proof, proof dependencies and proof origin to match.
Remote single-file compilation succeeded without warnings in 12.5 seconds.

## Proved and sorry left

Closed the one original hole in `WeilConjectures.nestedChosenScalarTensor_val_ext`
(node `lem-trf-nested-chosen-scalar-tensor-val-ext`). Original holes: 1; closed: 1;
added: 0; remaining in the delivered module: 0. No split-off statements.
The private helper `NestedChosenTensorProof.adjData` is proved in full.

## No longer needed

No modules or imports are removed. No new intermediate obligations are needed.
The original proof-dependency edge to
`def-trf-integral-comparison-realization-models` is replaced by the existing
finite-free scalar model and normalized ordinary adjunction nodes. The realization
module remains the original public statement import. No realization or Roos
comparison theorem is used, and no ancestor module or unit step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The former proof step described tensor induction and
sheafification abstractly, but did not name the existing normalized ordinary
coefficient adjunction. Its Hom equivalence proves this directly twice. No claim
that all sections of a sheafification are global pure tensors is needed. The unit
route and every existing statement are preserved. The assigned queue row is a
one-hole proof item; no matching rework row or build-error file was present.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.TraceFormula.NestedChosenScalarTensorValExt": "820562e1a912394165eae6c7aa1e0ba33e62d2c9"}, "results": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftNestedCoordinateComponentExtensionality": {"hash": "95d0f060abac7786785955c46603aa2557d103d3", "status": "OK"}}, "seconds": 70, "time": "2026-10-28T10:31:31+0800", "transitive": 0, "version": 1}
```

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
