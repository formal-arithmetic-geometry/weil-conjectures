## What changed

Restored Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact from its
quarantine archive, as required by coord/rework.tsv. Replaced the stale public import
Sheaf.CategoryTheory.CompactObject with
WeilConjectures.CategoryTheory.CompactObject, the canonical owner of the identical
CategoryTheory.IsCompactObject definition. This is the only source change against
the archive. The statement, docstring, complete proof, and DAG attachment are retained.

The proof specializes finiteRing_compactGenerators. Characteristic D.p follows
from the cardinality of D.k₀ and transfers to its algebraic closure D.k. The distinct
prime ℓ is therefore a unit. The proof extracts the existing coproduct witness and
compactness clause with exactly the given bounded-constructibility and finite-Tor
hypotheses. The zero ring, empty scheme and empty family are included unchanged.

Change record: coord/changes/D8-finite-tor-etale-compact-canonical-import.md.
No consumer signatures or definitions change. Both archived consumers are retained.
Remote single-file compilation passed without warnings in 2.6 seconds.
The restored Lean file has no lines over 100 characters and no sorry tokens.

## Proved and sorry left

This is a zero-hole restoration/import repair. The archive already contains a complete
proof of AlgebraicGeometry.Etale.finiteTorConstructible_etale_compact
(node det-ctf-finite-compact-etale). There were zero holes before the repair and there
are zero holes after it. Holes closed: none. Holes added: none. Split off: none.
The module uses the existing finiteRing_compactGenerators declaration, as planned.
No proof of that separate dependency is duplicated or replaced.

## No longer needed

Removed the empty, retired public import Sheaf.CategoryTheory.CompactObject;
its canonical upstream owner supplies the identical public notion instead.
No mathematical dependency, node or parent obligation is pruned. In particular,
lem-pur-etale-finite-ring-compact-generators and its proof-only module import remain.
All other original imports are retained. The unit route is unchanged.

The fresh LeanFinder search returned derived t-structure and bounded-representative
lemmas, no compactness result. Loogle for "IsCompactObject" returned zero hits.
Local source/Mathlib searches confirmed that the existing generator theorem is the
shortest available specialization route, and that the compactness definition's owner
has migrated to WeilConjectures. Import-direction checks permit both proof and
canonical-definition dependencies.

## Where the brief, the DAG or earlier work was wrong

The assigned source is absent from lean/, but this is quarantine rather than withdrawal.
Its archive must be restored. The earlier proof is sound; its public compactness import
became obsolete when the duplicate Sheaf definition was retired. The restored generator
theorem also imports the canonical definition publicly. No change to the DAG proof,
statement, source-library declaration or unit route is necessary.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
