## What changed

Proved `AlgebraicGeometry.Scheme.noetherian_complementary_stratifications` with its
statement and existing public imports unchanged. Added one proof-only import,
`WeilConjectures.Mathlib.Topology.Constructible`, for the already proved theorem that
locally closed subsets of a Noetherian space are constructible.

A fully proved private helper, `append_complementary_stratum`, constructs the same
partition for either ordering of the complementary immersions. Its index set is exactly
`Fin (S.n + 1)` and its dependent-pair family is exactly the requested `Fin.snoc`, so
the output equality is reflexive. Immersion composition, injectivity, the original
partition's coverage and disjointness, and complementarity prove every field. No witness
is chosen from an unproved existence theorem.

Mathlib supplies locally Noetherian sources, the Noetherian underlying spaces, compactness
of all subsets, quasi-separatedness, and quasi-compactness of the open immersion. Updated
the existing node's proof description to record these direct APIs; all original proof
dependencies and the unit route remain.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.noetherian_complementary_stratifications`
(node `lem-sfb-noetherian-complementary-stratifications`).

Added 0 holes; split off 0 statements; 0 holes remain in the delivery.
The private helper `append_complementary_stratum` is fully proved.

The complete module compiled on the project compile service without warnings (3.7 seconds).
A separate compile with `#print axioms` verified that the public theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`.
The construction does not require inhabited strata or a nonempty old index set: the
coverage proof obtains an old index only for points in the first immersion's image;
all other points are in the appended complement. Empty complements and empty strata
are retained with their exact given scheme structures.

## No longer needed

None. No public imports, dependency nodes, or modules were removed. All existing declared
proof dependencies still serve the proof, often through already proved Mathlib APIs.
No new proof dependencies on unfinished project declarations were introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. Constructibility of locally closed sets in a
Noetherian space is already proved in the adopted source-library extension
`WeilConjectures.Mathlib.Topology.Constructible`, rather than in Mathlib's constructibility
module itself. The proof uses that existing result. The DAG's geometric argument is valid;
the proof update records its direct Lean realization without changing the statement.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
