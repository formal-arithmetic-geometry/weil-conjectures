## What changed

Repaired reviewer C-e04cb points C (2/5) and D (6). Restored
`lean/Sheaf/Paper/EtaleCERowCyclesNaturality.lean` verbatim from
`quarantine/Sheaf/Paper/EtaleCERowCyclesNaturality.lean`, except line 10 now reads
`import all WeilConjectures.CategoryTheory.DoubleComplexTotal`. This keeps the
live Sheaf CE declarations used by both recorded consumers and preserves the
complete local proof and private row-inclusion API.

Restored the node attachment to `Sheaf.Paper.EtaleCERowCyclesNaturality`, with
`lean.existing` false and the original Sheaf file path. Updated
`proof_origin.place` to record the quarantine restoration and import switch;
the proof steps and dependency lists are unchanged. Removed the obsolete
`coord/changes/P3-etale-ce-row-cycles-upstream.md`, as requested: no signature
or definition changes in this repair.

The repaired module compiles through `lcompile.py`. A scratch consumer imports
both `Sheaf.Paper.EtaleCERowOrdinaryComparison` and
`Sheaf.Paper.EtaleCECanonicalRowComparison` alongside an `import all` of the
repaired module; it checks the original public statement and the private
row-inclusion API. Both files compile without errors or warnings. The axiom
probes for `etaleCE_row_cycles_naturality` and `rowInclusion_naturality`
report exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Zero-hole import repair: zero holes closed, zero holes added, zero holes left.
`AlgebraicGeometry.Etale.etaleCE_row_cycles_naturality` retains its complete
quarantined projection proof. All five private helper theorems are fully proved:
`rowProjection_inclusion`, `rowProjection_tail`, `rowInclusion_naturality`,
`rowProjection_naturality`, and `rowProjection_representative`,
with the two actual constructions `rowProjection` and `rowInclusion` unchanged.
No theorem is split off and no new node is added.

## No longer needed

Removed the returned draft's public import of
`WeilConjectures.AlgebraicGeometry.EtaleCERowCyclesNaturality`; its upstream CE
twins collide with the live Sheaf CE declarations. The quarantined direct
`Sheaf.CategoryTheory.DoubleComplexTotal` import is replaced by its
WeilConjectures twin. Both original Sheaf CE public imports and all local
helpers are restored.

No mathematical dependency node or module is pruned. Both recorded quarantined
consumers, the node dependencies, and the unit route are preserved. No source
library or quarantine file is changed; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior re-export repair mixed upstream CE twins with live Sheaf CE names,
causing the reviewer's consumer probe to fail with an existing
`AlgebraicGeometry.Etale.EtaleTermwiseHypercohomology._sizeOf_1` declaration.
It also attached the node to the upstream theorem although its statement
dependencies are Sheaf declarations. Restoring the quarantine proof with only
the lower-level DoubleComplexTotal import switched corrects both defects.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
