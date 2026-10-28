## What changed

Proved `WeilConjectures.canonicalIntegralPullbackTensor_scalar` from existing
normalized quotient realization theorems. Choose good representatives of
`![M, N, M]`, use `completedComparisonQuotientNormalization`, and identify the
coefficient-stage comparison transports with
`completedComparisonCanonicalIdentification` and
`completedComparisonScalarLimitImage`. The latter gives both scalar composites as
the same conjugated limit arrow. Transitivity and full-subcategory hom
extensionality finish the unchanged statement. The argument includes identity
scalar maps, ramified extensions, zero objects and empty schemes.

Extracted the existing integral constructor, reference comparison, counit theorem
and proved private sequence-ring identification into
`CompletedPullbackTensorIntegralConstruction`. Signatures and bodies are verbatim.
The assigned module publicly re-exports it. The unclaimed
`CompletedComparisonQuotientRealizationDefs` and
`ScalarExtensionTowerComparisonData` change only their relevant import to this
constructor, removing the import cycle through the scalar theorem. Four DAG
references are narrowed to the unchanged integral constructor; all citers remain
valid. No target or unit route changes.

After profiling and trying local transparency barriers, split the parent's
already-proved coherent section into `CompletedPullbackTensorCoherentConstruction`,
again retaining its declarations and proofs verbatim and publicly re-exporting
it. Retargeted the existing evaluation-data attachment. Also split the existing
proved model helpers from the unclaimed normalization module into
`CompletedComparisonQuotientNormalizationModels`. Its fully proved model theorem
supplies the good expressions, invertible substitutions, normalized reductions
and presentations; the original normalization theorem supplies its unchanged
naturality proof. No data construction, instance or public attribute changes.

Validation: all changed files and all 13 existing direct importers compiled
through `lcompile.py`, one file at a time in import order. Also compiled the
current finite and tower evaluation chain to check the counit consumer against
the moved declaration owners. The final full parent check took 46.3 seconds;
normalization took 31.2 seconds, and its model helper 26.3 seconds. The final narrow
check after coherent import cleanup passed in 17.9 and 45.7 seconds. All 30
original public declaration signatures are retained verbatim.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.canonicalIntegralPullbackTensor_scalar`.
No holes added or split off. All delivered Lean files have zero textual `sorry`
occurrences. The new `completedComparisonQuotientModels` theorem is fully proved;
the new modules also preserve all extracted complete proofs. Existing imported
realization obligations remain in their original modules with their existing
nodes and are not duplicated here.

## No longer needed

`CompletedComparisonQuotientRealizationDefs` and
`ScalarExtensionTowerComparisonData` no longer import
`Sheaf.Paper.CompletedPullbackTensorComparison`; they use the integral constructor
and existing tower data directly. The two counit proof imports moved into the
integral constructor. The coherent representative proof imports moved into the
coherent module. The normalization module uses its model helper instead of a
direct reduction-presentation proof import. The K-flat operations, normalized
reconstruction and legacy completeness proof imports moved from normalization to its model module. Redundant `import all`
access to the public realization definitions, and unused private imports of the
ringed tensor adjunction, strict quotient interface, strict scalar comparison,
sequence comparison systems and pro-etale implementation helpers were removed
where their proofs no longer use them. The new coherent module omits the unused
integral-constructor and ordinary canonical/open-square pullback imports, and keeps its K-flat proof import private.
Public re-exports from the original parent are preserved. No mathematical node,
unit or library module is withdrawn or pruned globally.

Historical parent proof steps belonging to the tower and coherent providers were
replaced by their provider nodes. The parent no longer directly cites:

- `def-coef-ringed-sequence-site`
- `def-trf-integral-comparison-sequence-systems`
- `lem-pur-integral-comparison-sequence-direct-evaluation`
- `lem-pur-ringed-site-module-pullback-exists-universes`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-ring-sheaves-grothendieck`

These facts remain in the provider dependency closures; they are not globally
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The needed quotient realization lemmas already existed, but an import of the
broad comparison module made them depend on the scalar theorem they can prove.
The constructor extraction and precise DAG references remove that artificial
cycle. Four statement-change records change only definition-node references;
no Lean statement, map, hypothesis or conclusion is changed.

The initial normalization and construction checks exceeded the per-file limit.
Profiling and local transparency barriers were tried before the proved sections
were extracted. Development profiler settings and attempted lint suppressions
were removed. An initial consumer check loaded an older published comparison
artifact containing the moved declarations; the current comparison source only
re-exports them. The final check includes its current naturality and comparison
modules, then the finite and tower evaluation modules, before the counit consumer,
so the affected chain is compiled in import order.

## New nodes

`def-pur-completed-pullback-tensor-integral-construction` owns the three existing
integral constructor declarations. It adds neither mathematical data nor a hole.

`lem-pur-completed-pullback-tensor-coherent-construction` owns the nine existing
proved coherent declarations. The old evaluation-data node follows its three
unchanged declarations to the extracted module.

`lem-pur-completed-comparison-quotient-models` records the fully proved model part
of normalization, excluding its separate naturality assertion. Its helpers and
assembly are the existing normalization proof; no obligation is split off. The
unrestricted normalized reconstruction and legacy completeness equivalence are
reused as generic tools, exactly as in the original normalization proof. They provide
the completeness and effective-counit identifications the construction needs;
no unit statement or step is bypassed.

Change record:
`coord/changes/T3-completed-pullback-tensor-integral-scalar.md`.

## Related modules compiled before delivery

12 related module(s) compiled against this delivery by deliver3.py: 5 INFRA, 7 OK.

```json
{"capped": false, "direct": 12, "left_out": 0, "own": {"Sheaf.Paper.CompletedComparisonQuotientNormalization": "faf657e01779fa6d01aa67053714c9438a67cb2c", "Sheaf.Paper.CompletedComparisonQuotientNormalizationModels": "517c0fbe5e429a241f98614e70f57824da042f14", "Sheaf.Paper.CompletedComparisonQuotientRealizationDefs": "a641c815405050e4b3cd3c99c5efe3d3ae1a8291", "Sheaf.Paper.CompletedPullbackTensorCoherentConstruction": "795e855f8cf042f10f08574c44a8c5d5055a5b80", "Sheaf.Paper.CompletedPullbackTensorConstruction": "dc3286b509deff76144acaecf65578a6dbd24008", "Sheaf.Paper.CompletedPullbackTensorIntegralConstruction": "cf47a410b3470c14777d9ffc118567e7edf771d6", "Sheaf.Paper.ScalarExtensionTowerComparisonData": "885b0b5282dad951d85f1e0993857fb560b3e05f"}, "results": {"Sheaf.Paper.CompletedComparisonCanonicalIdentification": {"hash": "68b807d65f524695c2f9d27b6a0580b2f6ff5071", "status": "OK"}, "Sheaf.Paper.CompletedComparisonQuotientRealization": {"hash": "796a7c0f0e18a4d00281d562698c417dac1b4495", "status": "OK"}, "Sheaf.Paper.CompletedComparisonScalarLimitImage": {"hash": "540a9bb2d786c463eedc2fe7de9e90d8ae1ee010", "status": "OK"}, "Sheaf.Paper.CompletedPullbackTensorComparison": {"hash": "fd66e69096d0ff4e4f87e781f097b7c02e6a79ba", "status": "INFRA"}, "Sheaf.Paper.CompletedPullbackTensorNaturality": {"hash": "6adde9c3226b1753c7fa06adcf8227b38bc8a7e2", "status": "OK"}, "Sheaf.Paper.CompletedQuotientReductionPresentation": {"hash": "b8303885b4ce0d71564cf97452d408ca031eec8e", "status": "OK"}, "Sheaf.Paper.IntegralPublishedCounitEvaluation": {"hash": "1292f016255ccc399868e111e36155cefecb5185", "status": "OK"}, "Sheaf.Paper.ScalarExtensionQuotientAssociation": {"hash": "f468fed4b4134179803b9837812a44cb5ed6ce06", "status": "INFRA"}, "Sheaf.Paper.ScalarExtensionQuotientAssociationDegreeData": {"hash": "7cd78266ebb132eee31da341e85468db9df178e0", "status": "OK"}, "Sheaf.Paper.ScalarExtensionTowerCoherence": {"hash": "efb8bde570c7822a88e3957c16202b262f2277a6", "status": "INFRA"}, "Sheaf.Paper.ScalarExtensionTowerComposition": {"hash": "1fceaf4a7531b4a16536d8c385497b8b29eb9b1b", "status": "INFRA"}, "Sheaf.Paper.ScalarExtensionTowerRealizationData": {"hash": "d6268383ff8fbbbe615f40cf68fd20e19912fff8", "status": "INFRA"}}, "seconds": 291, "time": "2026-10-28T02:59:57+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
