## What changed

Proved `AlgebraicGeometry.Etale.etaleCompactScalarOpenRestriction` in
`Sheaf.Paper.EtaleCompactScalarCoherence`, with its existing statement unchanged.
The proof identifies `ExceptionalCoefficients.openIso` with the canonical
`openScalarExtension` by equality of their inverse open-adjunction transposes.
It applies the existing open unit-mate cube argument to an arbitrary cartesian
open square, then pastes it with `exactDerivedBaseChangeMap_scalarExtension`.
Naturality of proper exchange and of the proper scalar mate gives the compact-support
square after `unboundedEtaleCompactSupport_exchange_normalization`.
Open restriction of a Noetherian scheme supplies the two auxiliary Noetherian instances.

Added proof-only imports of `Sheaf.Paper.EtaleOpenScalarExchange` (including its private
proved mate helpers) and `Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange`.
The three new private helpers are completely proved. Public signatures, definitions,
and public imports are unchanged. The proof follows step 6 of the existing node
`lem-pur-etale-compact-scalar-coherence`; its dependency list and route still apply.

Validation: the server single-file compiler accepted the resulting module, in 32.9 seconds.
The downstream proved raw exchange argument in `EtaleCompactScalarBaseChange` was
reused locally; that module itself cannot be imported here because it imports this item.
No other module was changed.

## Proved and sorry left

Closed one of the four original holes:
`AlgebraicGeometry.Etale.etaleCompactScalarOpenRestriction`.
Added zero holes and split off zero statements.

The following three original holes remain unchanged, all on node
`lem-pur-etale-compact-scalar-coherence`:

- `AlgebraicGeometry.Etale.etaleCompactScalarCoherence`.
- `AlgebraicGeometry.Etale.etaleCompactScalarComposition`.
- `AlgebraicGeometry.Etale.etaleCompactScalarUnit`.

This is a partial delivery of the multi-theorem module. The open-restriction proof
uses existing stated dependencies; it makes no boundedness or coefficient-flatness assumption.

## No longer needed

None. No existing imports were removed and no nodes or modules are withdrawn.
The remaining three holes still retain their existing planned dependencies.
The open-restriction proof uses the existing proper/open exchange route; it does
not introduce dependencies on projection or composition coherence.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The rework row records an earlier quarantine;
the current item source exists and was copied intact before proof edits. Its
unchanged baseline compiled successfully. Its attachment and dependencies are preserved.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
