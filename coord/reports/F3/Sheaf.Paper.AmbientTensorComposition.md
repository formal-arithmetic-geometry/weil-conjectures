## What changed

Replaced `WeilConjectures.AmbientPullbackTensor.normalizedTensor_composition` by a
complete proof of its unchanged ordinary, total-complex and derived assertions.
The ordinary square is checked through the composite adjunction on pure sections.
The chain square is proved for arbitrary complexes by the summand formulas.
The derived square uses the existing representative-composition calculation and
faithfulness of restriction to flat-term K-flat representatives. The generic chain and derived calculation is a new proved public theorem in
`Sheaf.Paper.TensorComparisonComposition`; its helpers are private and proved.
The ambient module adds only proof imports; its public import stays.
Updated the item's node to describe these arguments and their actual dependencies.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.AmbientPullbackTensor.normalizedTensor_composition`
(node `lem-sf-ambient-normalized-tensor-composition`).
No holes remain in either delivered module, no holes are added, and no
unproved obligation is split off. The new theorem
`WeilConjectures.SemilinearSections.tensorComparisonComposition` is also proved.
Validation: `lcompile.py --all` compiled both files without errors or warnings:
41.5 seconds for TensorComparisonComposition and 33.3 seconds for the ambient
item, each below 60 seconds. The original public signature was compared verbatim
and is unchanged. Delivery preflight performs the remaining mechanical checks.

## No longer needed

No original Lean import is removed. The proof does not directly import or use
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
(`lem-pur-cochain-pullback-tensor-coherence`): the shorter summand calculation
uses the given models and the existing `tensorSummand_map` helper.
`lem-pc-kflat-resolution` and `lem-weil-pbc-site-derived-tensor-descent` are
not separate direct proof dependencies: the resolving-pair extension is supplied
by `lem-sf-cochain-tensor-model-rigidity`, whose dependencies remain needed.
Likewise the ordinary calculation uses the independent-universe pure-section
extensionality helper, rather than importing the equal-universe
`lem-pc-sites-sheaf-tensor-bilinear-universal` statement.
The underlying tensor definitions and all transitive dependencies remain used;
no module is withdrawn and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The current server queue records a proof item
with one hole, and has no build-error or rework entry for it. The existing
`GeometricTensorEvaluation` module already contains the generic two-model
representative calculation needed by the final step. Reusing that calculation
avoids reimplementing tensor descent or choosing resolutions. The chain equation
in fact follows for all complexes; the original flatness hypotheses are retained
in the public statement.

## New nodes

`lem-coef-semilinear-tensor-comparison-composition`, in
`Sheaf.Paper.TensorComparisonComposition`, proves the chain and derived
composition squares for three abstract exact module functors from their ordinary
square. It has a complete proof and no `sorry`. Its private helpers perform the
summand calculation, representative pasting and faithful-restriction argument.
This proved general step is separated from the ambient generator calculation
because the combined file exceeded 60 seconds after the unfolding improvements.
No new obligation is split off, and no existing interface is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AmbientTensorComposition": "a333a7cc3b4dcd03e2dbd9a78326e58f1c49bd19", "Sheaf.Paper.TensorComparisonComposition": "50e5c37a0111044d73e043b3c765a3c6c925a14d"}, "results": {"Sheaf.Paper.AmbientPullbackTensorCoherence": {"hash": "227d4446696f1c275d91a1eed183a3de9f6b78a7", "status": "OK"}}, "seconds": 26, "time": "2026-10-28T06:49:15+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
