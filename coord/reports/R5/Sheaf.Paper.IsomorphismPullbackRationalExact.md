## What changed

Filled `WeilConjectures.isomorphismPullbackRationalExact` in
`Sheaf.Paper.IsomorphismPullbackRationalExact` using the complete proof preserved
in the earlier V3 delivery, checked against the current definitions. The earlier
delivery was withdrawn during an import-source quarantine event; this packet
works from the current restored source and preserves its public import of
`Sheaf.Paper.DerivedPullbackTensorHom`.

Added a private proof import of `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
The proof constructs the semilinear extension for the identity coefficient map,
proves that coefficient map is the identity by localization uniqueness, and
identifies the extension with the prescribed rational pullback by its unique
object and pure-tensor formulas. It applies `ScalarLocalization.extension_exact`
with the two published rational triangulation data, including the prescribed
shift normalization and the distinguished-image-triangle descriptions. The
statement, definitions and public imports are unchanged. Unused local attributes
and the unused algebraically closed coefficient namespace opening were removed.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.isomorphismPullbackRationalExact`
(node `lem-pod-isomorphism-pullback-rational-exact`).
No holes remain in the item and no holes were added or split off. This proves
the assigned theorem from the declared scalar-localization interface; it does
not claim that every transitive dependency of that interface is axiom-free.

## No longer needed

None. Every declared proof dependency is used: semilinear scalar localization,
the existing rationalization data, and the prescribed rational pullback.
No module or node is withdrawn. The existing public import is retained.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan fits the current interfaces without a statement repair
or a new intermediate theorem. The repository history contains a complete V3
proof, although the restored current source still has the original hole. The
archived V3 packet narrowed a public import to the finite/rational operations
module; this packet retains the current public import instead, avoiding an
unnecessary public interface change.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
