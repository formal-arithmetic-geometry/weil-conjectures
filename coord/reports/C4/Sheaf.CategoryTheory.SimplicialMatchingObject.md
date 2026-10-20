## What changed

Completed the retirement assigned by `coord/retire-items.tsv`, following the human's
hand-off in `coord/changes/retire-sheaf-twins-20261020.md`.
`Sheaf.CategoryTheory.SimplicialMatchingObject` is withdrawn using `deleted.txt`.
All eight direct importers now import the upstream twin
`WeilConjectures.CategoryTheory.SimplicialMatchingObject` with the same import visibility:

- Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
- Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry
- Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverWeak
- Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember
- Sheaf.CategoryTheory.MatchingObjectCoskeleton
- Sheaf.CategoryTheory.SiteHypercoverDisjointUnion
- Sheaf.Paper.CondensedHypercoverComparison
- Sheaf.Paper.CondensedHypercoverInjectiveRow

Only Geometry, SRMatchingObjectOneMember, and SiteHypercoverDisjointUnion used the
removed theorem exports. In their existing proofs, the degree-one cone is now the
canonical fan limit, and its matching arrow is the fan lift of the two faces.
In higher degrees, the cone is the canonical finite multiequalizer, and its arrow
is the multifork lift of the compatible faces. Compatibility is proved by reindexing
Mathlib's `SimplicialObject.δ_comp_δ` with `a ≤ b - 1` for `a < b`.
The projection equations are the corresponding Mathlib `IsLimit.fac` lemmas.
Every surviving declaration signature is unchanged. No upstream file is changed.

The existing node `lem-weil-pbc-simplicial-matching-object` now attaches to the actual
upstream boundary definitions. Its note distinguishes those definitions from the
withdrawn existence/uniqueness theorem exports and identifies the consumer proofs
which now construct the needed objects. The node's mathematical statement, proof,
proof dependencies, and unit route are unchanged. No new nodes or declarations.

Validation: all eight adapted modules compiled cleanly together through `lcompile.py
--all`, in dependency order. Reported times were 9.9, 2.2, 3.1, 2.5, 33.7, 1.8, 2.7,
and 6.5 seconds respectively in the compiler's order. No source line exceeds 100
characters. Dry run `c0668d8bc2` passed the preflight with review class CODEX.
The delivery tool's full-module axiom probes timed out for Geometry,
CondensedHypercoverComparison, and CondensedHypercoverInjectiveRow; it reports
that the merge repeats those probes. These were probe timeouts, not normal
single-file compilation failures. A separate 2.4-second imported check against
this sandbox's compiled modules ran `#print axioms` for
`exists_properFaceMatchingArrow`, `etaleFaces`,
`exists_affine_hypercover_geometry`, `condensedHypercover_comparison`, and
`condensedHypercoverInjectiveRow`: every result lists exactly `propext`,
`Classical.choice`, and `Quot.sound`. Thus all changed proof consumers and the
two condensed-hypercover public results have been checked directly.
Change record: `coord/changes/simplicial-matching-object-retirement.md`.

## Proved and sorry left

The assigned module already had zero sorries: 0 holes closed, 0 added, 0 left;
this is a retirement repair, not new proof progress. No split-offs.
The adapted modules also contain no sorry.

The removed, already-proved exports are
`CategoryTheory.SimplicialObject.matching_object_zero`,
`CategoryTheory.SimplicialObject.matching_object_one`, and
`CategoryTheory.SimplicialObject.matching_object_succ_succ`.
The needed existence and projection facts are proved directly in
`CategoryTheory.SimplicialObject.exists_properFaceMatchingArrow` (private),
`AlgebraicGeometry.Scheme.etaleFaces` (private), and
`AlgebraicGeometry.Scheme.ProEt.exists_affine_hypercover_geometry`.
They use Mathlib's proved limit and face-identity API; nothing is assumed anew.

## No longer needed

Pruned `Sheaf.CategoryTheory.SimplicialMatchingObject`: removed its eight import
references and withdrew its file. Every consumer uses the actual upstream boundary
definitions. No Lean source in the delivered set refers to the withdrawn module.
The generic unique-terminal-isomorphism, unique-limit-isomorphism, and natural tuple
bijection exports have no consumers; none is reintroduced under a new name.
The node is retained and reattached, not deleted. The three declared DAG proof
dependencies (finite limits, simplicial objects, face identity) remain needed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving holes, but the actual queue entry has kind
`retire`, and the assigned module's three holes were already proved in D2's
2026-10-15 delivery. The retirement hand-off requires adapting the consumers and
withdrawing the wrapper. The upstream twin lacks the three theorem exports, so
simply changing imports would fail at six proof calls; these calls are replaced
by explicit finite-limit constructions, with no new assumptions or weaker results.

The old node record listed the boundary definitions as declarations of the Sheaf
wrapper even though they come from its upstream import. The new attachment names
the actual upstream definitions and explicitly avoids claiming that the twin has
the full old theorem signatures. No mathematical statement was changed.

The optional `tools/import_direction.py may` check initially raced with another
writer deleting an unrelated source file and raised FileNotFoundError. Its retry
succeeded. No tool was modified. No stage-3 section I exists in the current
`coord/delivery-errors.md`; its existing sections were inspected.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
