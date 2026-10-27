## What changed

Restored `Sheaf.Paper.DerivedPullbackTensorIso` from its preserved quarantine source,
retaining every declaration, definition, proof and import. Scoped the local caches for
constructibility and linear Hom data to the rational coherence block, so the later
abstract tensor-induction proof keeps its original elaboration context.
Disabled the expensive section-variable, variable and private-module style scans locally,
as in the operation module this file consumes.

Before the final common-stage proof, kept the full-subcategory category, localized
category/module and stage-system data folded locally. The final assembly also keeps
the canonical common-stage comparison folded. No exported attribute or instance changed.

Validation: the complete item compiled through `lcompile.py` in 53.5 seconds (exit 0).
No diagnostic options, output commands or temporary Lean modules remain in the delivery.

This is the assigned rework/restoration repair. No definition data or theorem signature changed.
Change record: `coord/changes/J4-derived-tensor-coherence-elaboration.md`.
The record lists all direct importers; local options and attributes do not change their interface.

## Proved and sorry left

Closed zero of the eight existing theorem holes; added zero holes. All existing completed
proofs and canonical constructions are retained. The eight remaining holes, all attached to
`lem-pur-derived-pullback-tensor-iso`, are:

- `WeilConjectures.pullbackTensorCommonComposition_existsUnique`
- `WeilConjectures.pullbackTensorCommonAssociator_existsUnique`
- `WeilConjectures.pullbackTensorCommonBraiding_existsUnique`
- `WeilConjectures.pullbackTensorRationalScalarUnit_existsUnique`
- `WeilConjectures.pullbackTensorCommonLeftUnitor_existsUnique`
- `WeilConjectures.pullbackTensorCommonRightUnitor_existsUnique`
- `WeilConjectures.canonicalCommonStagePullbackTensor_associative_spec`
- `WeilConjectures.derivedPullbackTensorIso`

## No longer needed

None. No import, declaration, module, DAG dependency or unit-route step is removed.
The quarantine archive and all five existing node attachments are preserved.

## Where the brief, the DAG or earlier work was wrong

The item was initially absent from `lean/`, but the rework row preserved its original
source at `quarantine/Sheaf/Paper/DerivedPullbackTensorIso.lean`. Its absence did not
justify withdrawing its declarations. The archive's unchanged file exceeded the compile
limit; importing the same dependencies without the declarations took 3.4 seconds.
Profiling and prefix builds isolate the slow checking to the final common-stage
section or assembly: the prefix through rational braiding compiles in 33.8 seconds.
The rational associativity proof itself finishes in about six seconds with the cached
Hom structures. Those caches must be scoped: otherwise they interfere with the later
abstract tensor-induction simplifications and duplicate a subsequent local attribute.
Broad expression tracing is too expensive here and is absent from delivery.
The proof route itself is unchanged, so no DAG proof field needs changing.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
