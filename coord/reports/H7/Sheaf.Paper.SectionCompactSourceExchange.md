## What changed

Extracted the unchanged source-map declarations into
`Sheaf.Paper.SectionCompactSourceMaps`, publicly reexported by the original module.
This lets separate exchange components refer to the prescribed maps without a cycle.
The target statement and the composition-normalization statement remain unchanged.
The target proof assembles four invertibility clauses, the etale exchange component,
and its pro-etale transport. A private mate calculation identifies the supported
comparison with the ordinary closed direct-image comparison.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.SectionCompactSource.section_compact_source_exchange` is closed
by a decomposition, not an independent proof of its new component obligations.
`AlgebraicGeometry.SectionCompactSource.composition_normalization` remains sorry
(node `lem-pur-section-compact-source-exchange`).

New holes are:
- `AlgebraicGeometry.SectionCompactSource.etale_section_exchange_component`
  (`lem-pur-section-source-etale-exchange`).
- `AlgebraicGeometry.SectionCompactSource.pro_section_exchange_component`
  (`lem-pur-section-source-pro-exchange`).
- `AlgebraicGeometry.SectionCompactSource.supported_pro_exchange_isIso`
  (`lem-pur-section-supported-pro-exchange-iso`).

The new `AlgebraicGeometry.SectionCompactSource.supported_comparison_isIso`
(`lem-pur-section-supported-comparison-iso`) is proved, as are all private helpers.
Thus 1 of the 2 original holes is closed and 3 holes are added: this is a decomposition.
All six delivered Lean modules compiled together with exit code 0. No data definition
contains a hole.

## No longer needed

Removed the unused proof-only imports `Sheaf.AlgebraicGeometry.OpenClosedRecollement`,
`Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`,
`Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization`,
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`, and
`Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients` from the item and extracted map module.
The still-open composition-normalization obligation and component arguments retain their
DAG dependencies, so no existing node or module is withdrawn. No scratch file is delivered.

## Where the brief, the DAG or earlier work was wrong

The resumed attempt's disk-space failure is no longer present. The earlier proof tried
to infer isomorphisms across semireducible site/category interfaces, which required
explicit comparison components. The extraction preserves the unit's source normalization
and both exchange steps. The new component equations are strict parts of the original
conjunction and impose no finiteness or Noetherian assumption on the new base.

## New nodes

`lem-pur-section-source-etale-exchange` records the proper/open and identity-mate
calculation. Its theorem is in `Sheaf.Paper.SectionSourceEtaleExchange`.

`lem-pur-section-source-pro-exchange` records transport of that equation through the
actual compact-support site comparison. Its theorem is in
`Sheaf.Paper.SectionSourceProExchange`.

`lem-pur-section-supported-comparison-iso` records invertibility of the canonical
closed supported-constant comparison. Its theorem is in
`Sheaf.Paper.SectionSupportedComparisonIso`.

`lem-pur-section-supported-pro-exchange-iso` records invertibility of the actual
underived pro-etale closed exchange. Its theorem is in
`Sheaf.Paper.SectionSupportedProExchangeIso`.

Change record: `coord/changes/H7-section-source-component-interface.md`.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
