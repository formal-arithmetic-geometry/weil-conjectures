## What changed

Proved `WeilConjectures.FiniteFieldDatum.absoluteFrobenius_isUniversalHomeomorphism`
in `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusUniversalHomeomorphism`, preserving its
signature, visibility, documentation, and imports. A proved private helper establishes
naturality of the constructed iterate using `map_pow` (the argument of Stacks,
varieties.tex, lemma-frobenius-endomorphism-identity). On an arbitrary affine test
scheme, global sections identify the iterate with the prescribed power map using
`Nat.card D.k₀ = D.p ^ D.a`. Naturality then proves `IsFrobenius`, allowing application
of the already proved upstream `Scheme.Hom.IsFrobenius.isUniversalHomeomorphism`.
This is the route already specified in the item's docstring and node's source/candidate;
no DAG route or statement changes. The proof applies to empty schemes and zero affine
rings, and adds no finite-type or separatedness hypotheses.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.FiniteFieldDatum.absoluteFrobenius_isUniversalHomeomorphism`
(node `lem-pur-absolute-frobenius-universal-homeomorphism`).
Added 0 holes; 0 holes remain in the module. No statements were split off.
The completed module compiles without errors or warnings.

## No longer needed

None. Both existing public imports are used; the node has no declared proof
dependencies to prune. No nodes or modules are bypassed by a change of route.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The documented upstream theorem requires the affine
`IsFrobenius` predicate, so the constructed iterate needs the explicit compatibility
proof supplied here. Searches with LeanFinder, Loogle, and grep found no closer Mathlib scheme theorem;
the existing source-library theorem supplies the full universal-homeomorphism argument.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
