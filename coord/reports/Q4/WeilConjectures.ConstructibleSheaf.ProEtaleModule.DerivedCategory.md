## What changed

Completed the existing theorem
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_of_weakSerre` in
`Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`, an unclaimed companion module
that states the reviewed correction of this item's false assertion. Its proof
identifies bounded constructibility with boundedness intersected with the derived
homology property, then applies the existing instances for weak Serre classes and
intersections. No new imports are needed and no declaration signature is changed.

In the assigned module, added a STATEMENT-DISPUTED comment at
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible`, explaining the
noncoherent-ring counterexample and naming the true theorem. Its signature and hole
are retained under the source-library boundary. This delivery is partial progress,
not a proof or repair of the false arbitrary-ring assertion.

The companion and original modules compiled individually with lcompile.py in 5.8 and
6.5 seconds respectively before the dispute comment was added. Delivery validation
checks the final versions again. The proof follows the existing weak Serre route;
no DAG route or unit statement changes are proposed.

Change record: `coord/changes/Q4-bounded-constructible-weak-serre-proof.md`.

## Proved and sorry left

Assigned module: zero of one original holes closed. The remaining hole is
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible` (the false upstream
instance, historically recorded in the audit of `sk-def-sfb-bounded-constructible`).
The currently attached definition node `def-sfb-bounded-constructible-complexes`
describes bounded constructibility, not a proof of this false instance.

Companion module: one of one original holes closed,
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_of_weakSerre`
(blueprint `sk-def-sfb-bounded-constructible`, whose reviewed statement explicitly
requires the weak Serre closure hypotheses). No holes remain in that module.

Total across the two delivered modules: two original holes, one closed, one retained,
zero added, zero split off. No definition contains a new hole. The proof is complete
from existing declarations, and never applies the disputed upstream instance.

## No longer needed

No imports removed, no modules withdrawn, no nodes pruned. The original module has
no declared proof plan for its false instance. The companion proof uses the already
imported general homology-property and bounded-intersection machinery; no coefficient
specialization, scalar-extension result or newly stated intermediate lemma is required.
The unit route and all current dependency records are preserved.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: topological noetherianity of X does not imply finite presentation
of kernels for arbitrary coefficient rings. Let k be a field and B = k ⊕ V the
square-zero ring for an infinite-dimensional k-vector space V. Multiplication by a
nonzero v in V on B has kernel V: (a,w)(0,v) = (0,av). Its B-action factors through k,
so V is not finitely generated over B. Both source and target are free of rank one.
The cone has this kernel as cohomology. Constant discrete coefficient and module
sheaves over a geometric point realize this obstruction on a noetherian base.

This is the same dispute already reviewed in the B4 and C4 reports and in the current
node `sk-def-sfb-bounded-constructible`, whose corrected weak Serre statement is true.
The upstream sync restored the original false instance. The original declaration is
absent from `coord/upstream-statement-exceptions.tsv`. Hence the source boundary forbids
replacing it with the corrected signature or removing it, and proving the true
conditional version does not close the original hole. The maintainer must reconcile
that upstream signature with the reviewed mathematical correction. A clarification
request was submitted during this session; absent authorization, no signature is changed.

The companion's existing hole is independently solvable using the already proved
upstream homology-property theorem, so this delivery closes it without moving or
renaming any obligation. The current DAG's generic weak Serre plan already describes
that proof; there is no mathematical change to its statement or route.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
