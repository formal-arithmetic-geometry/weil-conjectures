## What changed

Restored the assigned quarantined module at its original live Lean path. Replaced the
retired `LocallyClosedStratification` abbreviation in `IsSfbStratifiedPerfect` by its
defining type, `Scheme.Stratification`, and replaced its empty Sheaf import by the
canonical upstream module with the same public visibility. This repairs the recorded
unknown-identifier failure without changing the elaborated predicate or theorem.

The restoration preserves every declaration, the existing theorem proof, both DAG
attachments, all parent dependencies, and the integral-models unit route. Change record:
`coord/changes/R4-adic-stratified-perfect-restoration.md`.

## Proved and sorry left

This is the assigned quarantine/interface repair, not a proof completion. Holes closed:
none. Holes added: none relative to the preserved quarantine source. The one existing
hole remains `AlgebraicGeometry.Scheme.adic_stratified_perfect`
(node `lem-sfb-adic-stratified-perfect`). There are no holes in
definitions. No statements were split off.

## No longer needed

The empty retired module `Sheaf.AlgebraicGeometry.LocallyClosedStratification` is replaced
by `WeilConjectures.AlgebraicGeometry.LocallyClosedStratification`. No mathematical node,
proof dependency, or parent module is pruned. All existing proof imports are retained:
their removal is outside this restoration. The quarantined archive is not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The upstream sync left the archive referring to a retired alias. The landed F9 retirement
record identifies it as exactly `abbrev LocallyClosedStratification X := Stratification X`.
Using `FiniteLocallyClosedStratification` instead would choose a different structure;
the repaired definition uses the original defining type. Constructibility is still
explicitly required by the predicate. Empty schemes and strata, zero complexes, the
cover quantifiers and all coefficient/model bounds are unaffected.

The two attached nodes already record the retained declaration signatures without the
retired alias, so neither needs a semantic or proof-dependency update. The original
six-step proof remains unfinished, with its source and full proof in the docstring.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
