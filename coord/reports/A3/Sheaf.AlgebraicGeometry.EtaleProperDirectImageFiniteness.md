## What changed

Restored `lean/Sheaf/AlgebraicGeometry/EtaleProperDirectImageFiniteness.lean`
from its preserved quarantine archive, as assigned by coord/rework.tsv (upsync
5f7b33eac). The archive is retained unchanged.

The archived proof failed to compile because its four applications of
`Scheme.isConstructibleEtaleModuleSheaf_iff` refer to a retired duplicate.
Replaced the private proof import with
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`
and all four applications with the canonical theorem
`Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`.
The two equivalences have identical signatures. The restored file compiles
cleanly through lcompile.py (33.8 seconds).

The theorem signature, public imports, definitions, proof route, node attachment,
and all DAG dependency edges are preserved. The existing node already describes
the retained proof, so no node edit is necessary. No consumer requires adaptation:
the restored public interface is identical to the archive.

Change record: `coord/changes/A3-etale-proper-direct-image-finiteness-restoration.md`.

## Proved and sorry left

This is a zero-hole repair. The archive contains zero `sorry`s, and the restored
module contains zero. `AlgebraicGeometry.Etale.proper_directImage_finiteness`
(node `lem-weil-pbc-etale-proper-direct-image-finiteness`) retains its complete
proof. Holes closed: 0; holes added: 0; split off: 0. No other Lean module is changed.
This restoration is not counted as a newly closed hole.

## No longer needed

Removed the private reference to the retired duplicate module
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` and its short
comparison name. Its mathematical node
`lem-weil-pbc-constructible-etale-module-sheaf-comparison` remains needed and is
used through its current canonical source-library attachment.

No mathematical nodes or proof dependencies are pruned. The identity
compactification, compact-support constructibility, finite-coefficient geometric
base change, relative torsion dimension bound, and geometric-stalk conservativity
are all still used. The other imports remain necessary for these constructions
and their comparison isomorphisms. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because it is quarantined, not withdrawn.
The preserved archive was already proved but had not received the canonical
comparison import and name migration documented in
`coord/changes/D9-constructible-etale-module-comparison-retirement.md`.
The initial compile reproduced the four unknown-constant errors; the migrated
copy compiles. No mathematical statement or definition defect was found.

Read the current node and its recorded dependencies, the unit realization and
latest blueprint unit. The retained proof does not change the unit route.
Searches with msearch leanfinder and loogle found no Mathlib replacement. Source
search found the proper constructibility theorem in
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper`, but it requires
finite type over a field; it does not replace this arbitrary Noetherian-base
statement. Retained the existing proof rather than specialize the theorem.

Consumer check: tools/downstream.py reports an unknown module because the item
is quarantined. A source import-graph scan including lean/ and quarantine/ finds
four direct consumers and 47 transitive consumers, all quarantined. The change
record lists them. The only direct declaration calls are in
`Sheaf.Paper.PbcFiniteDirectImageCohomology` and
`Sheaf.Paper.ProperDirectImageFiniteness`; their argument lists remain valid
because the restored signature is unchanged. The quarantine sources are preserved.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
