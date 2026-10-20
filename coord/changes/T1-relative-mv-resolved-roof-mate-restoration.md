# AlgebraicGeometry.relativeMV_resolved_roof_mate_comparisons

## Reason

Restore the complete, zero-hole module from its quarantine path recorded in
`coord/rework.tsv`. The archive exceeds the unchanged 60-second single-file
compile limit against the current dependencies. Upstream now declares
`derivedPullback` with `irreducible_def`, so the redundant local irreducibility
entry must also be removed.

## Old

```lean
attribute [local irreducible] derivedPullback Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh
```

The archived proof uses the default abelian-instance priority and lets comparisons
unfold `RingedSpace.moduleDirectImage`.

## New

```lean
attribute [local instance 2000] schemeMVModuleAbelian
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh RingedSpace.moduleDirectImage
set_option backward.defeqAttrib.useBackward true
```

These local elaboration controls keep the fixed direct-image functors folded and
select the same module-sheaf abelian structure directly. The public theorem now
respects these transparency boundaries. Five proved private helpers perform the
first-component transport and calculation, denominator transport, adjunction
naturality, and existential assembly for abstract categories. Statement aliases
are reduced once with projection reduction disabled. The first inverse receives its existing isomorphism proof
explicitly, avoiding repeated instance synthesis through the row aliases.
The theorem statement, docstring, mathematical proof route and all five imports
are preserved. The heartbeat budgets decrease from 800000 to 50000 for the
global-transpose helper and from 1000000 to 200000 for the public theorem.
The final inverse comparison uses congruence after normalizing the component
identities, so no unexposed inverse body is unfolded. The complete repaired
proof compiled in 39.3 seconds with no errors or warnings.
No data definition, source-library declaration, target or public signature changes.

## Users

`tools/downstream.py` reports the live module as unknown because it is quarantined.
Direct searches of both library roots and the quarantine archive find the sole
archived direct importer below. Its theorem application supplies the identical
arguments and consumes the same six isomorphisms and three equations. No consumer
adaptation is needed. The archive and its dependencies are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMateComparisons | T1 | Restore and repair compilation. |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofVertexNormalization | unclaimed in shared snapshot (quarantined) | Public signature unchanged; no adaptation. |

## Status

landed 20261020T235626-L-1197487 2026-10-20 (merge of deliver/T1/Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMateComparisons)
