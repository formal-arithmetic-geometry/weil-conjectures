## What changed

Completed the zero-hole retirement listed in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian`.
The duplicate is withdrawn through `deleted.txt`; its mathematical node is reattached
to the proved upstream owner
`WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian`.

Adapted the sole direct consumer,
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient`.
Its proof now composes the supplied ring map with `smallStrictHenselizationColimitIso`,
uses its existing `comparison_base` lemma to verify the full-colimit structural-map
hypothesis, applies upstream Noetherianity, and transfers it along the inverse ring
equivalence with `isNoetherianRing_of_ringEquiv`. The existing quotient transport now
shares that same comparison. The consumer's theorem signature, visibility, universes,
public imports and docstring are unchanged; no source-library file is changed.
Both mathematical nodes keep their dependency edges. Their proof text records the
retained upstream proof and the consumer's explicit transport.

Change record:
`coord/changes/R4-retire-strict-hensel-regular-divisor-quotient-noetherian.md`.

## Proved and sorry left

The item already has zero holes. Closed zero existing sorries; added zero sorries;
split off zero statements. No remaining sorry declarations in the delivered code.
The retained upstream declaration
`AlgebraicGeometry.Scheme.strictHenselizationRing_noetherian_of_regular` and the
adapted consumer `AlgebraicGeometry.Scheme.strictHenselization_regular_divisor_quotient`
are proved. This is a retirement and a proved consumer adaptation, not a net hole closure.

The adapted consumer compiles cleanly through `lcompile.py` with the item compiled
as an empty module. Its original source fails against the empty module at line 87:
`Unknown identifier strictHenselizationRing_noetherian_of_regular`.
All eight downstream modules compile cleanly in import order against the adapted
consumer and the empty item, through `lcompile.py --all`. An unchanged verification
copy of `SmallStrictHenselizationIndEtale` supplied its missing published artifact;
it and all unchanged downstream verification copies were removed before delivery.
The final delivery preflight checks compilation and declaration axioms.

## No longer needed

Pruned the duplicate module
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian`
and its private import in the combined quotient consumer. That import is replaced
by the proved upstream owner. The retired file's private imports of
`WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular`
and `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility` leave with the file;
these modules remain needed elsewhere and are not withdrawn.

No mathematical dependency nodes are pruned. The Noetherianity node remains attached
to its upstream theorem, with the regular-divisor quotient and local-structure edges
retained. Its sole DAG parent remains the combined regular-divisor quotient node.
No new modules, nodes or imports beyond the retained upstream owner are needed.
The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item containing `sorry`; the current queue
and retirement table actually assign a zero-hole duplicate retirement. A no-op or
a simple import replacement would not complete this task: the two theorem signatures
use canonically isomorphic but distinct colimit rings and structural maps. The
consumer therefore performs the full structural-map and ring-property transport.

Checked all DAG statement dependencies, proof dependencies and proof-step uses:
only the combined quotient node cites the item. No quarantined module mentions the
retired module or declaration. `tools/downstream.py --uses` lists eight downstream
modules, with only the combined quotient as a direct caller. All were unclaimed
when checked. No target statement, definition or adopted source declaration changes.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
