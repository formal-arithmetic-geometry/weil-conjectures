## What changed

Retired `Sheaf.AlgebraicGeometry.ExternalConstantSectionsTensorMap`, listed in
`coord/retire-items.tsv`, and reattached
`lem-sc-external-constant-sections-tensor-map` to the existing adopted-source
`externalConstantSectionsTensorMap`, its `_app` formula, and its
`_app_bijective_iff` theorem. These supply exactly the map and criterion of
`exists_external_constant_sections_tensor_map`. Updated the sole DAG parent's
proof text to describe the named API already used by its unchanged Lean proof.

The exact old existential statement compiles from the upstream map and criterion
in 2.0 seconds. Its axioms, and those of both upstream declarations, are only
`propext`, `Classical.choice`, `Quot.sound`. The unchanged adopted-source parent
`PicardExternalCoefficientsPushforwardTensorComparison` compiles in 4.5 seconds.
All compilation used `lcompile.py`; validation files remain in `scratchpad/`.

Change record: `coord/changes/M8-retire-external-constant-sections-tensor-map.md`.
No source-library declaration, signature, attribute, public import, or body changes.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero split off.
The retired `AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_map`
was already proved. No `sorry` is left or introduced by this delivery.
This is duplicate retirement, not a proof-progress claim.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.ExternalConstantSectionsTensorMap` and its duplicate
existential theorem. Its imports disappear with the retired module:
`WeilConjectures.AlgebraicGeometry.PicardConstantSectionsTensor`,
`Sheaf.Paper.PQFCohomology`,
`WeilConjectures.AlgebraicGeometry.ExternalSectionsComponents`, and
`WeilConjectures.AlgebraicGeometry.PicardConstantTensorBalancedSections`.
Their declarations remain needed by the adopted-source implementation; none of
those modules or DAG dependencies is withdrawn. No additional node is pruned.

The sole DAG parent already imports the upstream module and uses the explicit
map and criterion. `tools/downstream.py` reports zero Lean importers; searches
also checked quarantined sources and unit realizations. All parent dependencies
remain, attached to the replacement construction. No unfinished parent loses
an obligation and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

This is the listed retirement of a zero-hole module, rather than a remaining
proof hole. The old retirement inventory says the upstream twin lacks the
existential wrapper; it nevertheless supplies the explicit map and exact
criterion needed to recover that statement. The DAG attachment was stale:
its sole parent already uses this adopted-source API directly. The delivered
reattachment reconciles the DAG with that current Lean proof.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
