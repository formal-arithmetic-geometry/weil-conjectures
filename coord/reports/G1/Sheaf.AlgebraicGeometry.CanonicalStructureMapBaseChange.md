## What changed

Restore Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange from its assigned
quarantine archive. Preserve the complete public statement, all six imports, its
canonical maps and all DAG dependencies. Replace the expensive private pullback
naturality proof by composition of the three mapped naturality squares, with two
proved private category helpers. The tensor structure transport, pushforward
naturality and main ordinary-unit/derived-comparison argument remain intact.
No source-library file changes, new public declarations or new nodes.

Change record: coord/changes/G1-canonical-structure-map-base-change-restoration.md.
The existing node's Lean attachment records the restoration.

## Proved and sorry left

This is a restoration repair with 0 original direct holes and 0 final direct holes.
AlgebraicGeometry.canonical_structure_map_base_change
(node lem-sc-canonical-structure-map-base-change) retains a complete proof.
Holes closed: none (0 of 0). Holes added: none. Sorries left: none.
Split-off theorems: none. No net hole reduction is claimed.

Validation: the actual restored module, importing the published dependency and
applying canonicalSingleBaseChangeComparison directly, compiles through lcompile.py
in 15.8 seconds with no errors or warnings. The archived private helpers alone took
53.5 seconds. All Lean lines are at most 100 characters. A direct textual comparison
confirms that the public theorem signature is unchanged verbatim from the archive.

## No longer needed

None. Every original import, node, declaration and proof dependency is retained.
The ordinary structure-sheaf adjunction lemma is used in tensor_structure_transport;
the canonical pullback/direct-image constructions and derived exchange occur in
the statement; canonicalSingleBaseChangeComparison and moduleBaseChangeMap_algebra
are used in the proof. No parent or unit step is pruned. In particular, the
quarantined FlatDerivedStructureUnitProperties parent remains an obligation.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes filling holes, but the assigned rework archive
has zero direct holes. The required work is restoration, including the complete
proof, rather than withdrawal based on the absent live path. The full naturality
argument is already in the archive; its slow localized rewrites can be replaced
by composition of ordinary categorical naturality squares without changing the
mathematical route or selecting additional data.

Read Stacks cohomology.tex, remark-base-change (Tag 08HY), and sheaves.tex,
lemma-adjoint-pullback-pushforward-modules (Tag 0096). The statement imposes no
cartesianness, flatness, invertibility or nonemptiness assumption, and the proof
uses none. No unit route is bypassed. LeanFinder found only ordinary structure
map results, Loogle found the exact ordinary unit-transpose lemma used here, and
launcher grep found no full derived structure-map identity. Local searches found
the existing single-base-change comparison, which is used rather than restated.

The source-only downstream query cannot inspect an absent module; scanning the
archive and DAG finds exactly the preserved parent described in the change record.
There is no open item-specific return in coord/returns/G1.md.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
