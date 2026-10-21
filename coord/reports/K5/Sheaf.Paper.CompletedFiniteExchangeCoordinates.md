## What changed

Completed the two remaining proofs in
`Sheaf.Paper.CompletedFiniteExchangeCoordinates`. Private, proved helpers identify
finite open pullback with restriction through the constant-ring comparison and
transport extension by zero through the slice equivalence. The second proof uses
full faithfulness of extension by zero and its essential image to show that the
specified mate is invertible. All existing public signatures and public imports
are preserved. Proof-only imports provide the existing slice, scalar-restriction,
and adjunction transport results.

Updated the proof route, proof dependencies, and proof origin of
`def-cbc-completed-finite-exchange-coordinates` to describe these arguments.
No public definitions, target statements, or source-library files changed.
The local proof-environment commands are documented in
`coord/changes/completed-finite-exchange-proof-environment.md`. Continuity helpers
are registered as instances only locally; no new global instances are exported.

## Proved and sorry left

Closed both existing holes:

- `AlgebraicGeometry.Scheme.cbcFiniteOpenRestriction_existsUnique`.
- `AlgebraicGeometry.Scheme.cbcFiniteOpenRes_isIso`.

Two holes closed, zero holes added, zero holes remaining in the item, and zero
statements split off. Every new private helper is proved. The proofs use existing
declared dependencies, including the scalar-restriction comparison
`cbcOpenRestrictIso_existsUnique`; this delivery does not close holes in those
dependencies. All 36 existing public declaration signatures were checked against
the current source and remain unchanged. The corrected module compiled successfully through `lcompile.py` in 37.8 seconds
with no diagnostics. The delivery tool performs its own compilation and preflight.

## No longer needed

None. No original imports, modules, or nodes are withdrawn. The categorical
full-faithfulness argument avoids constructing another explicit inverse on
extension summands, while retaining the existing slice comparison and the unit's
route.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was found false. The earlier proof record described
the two unfinished obligations without discharging them. The updated record
supplies the actual constant-ring and adjunction arguments. For the second
obligation, the known slice isomorphism places the target in the essential image
of the fully faithful completed extension; the invertible adjunct then proves
invertibility of the specified mate, without a separate summand-level inverse.

Preflight requested the proof-environment change record above; the initial
private-instance registrations were replaced with local instance attributes.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
