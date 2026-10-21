## What changed

Restored `lean/Sheaf/Paper/SitePerfectComplex.lean` from its exact quarantine
archive listed in `coord/rework.tsv`. Repaired `IsRationalFiniteProjectiveTerm`
by specifying `(integralTowerModules l E Y)` instead of `_` as the category
argument of the four `DerivedCategory.singleFunctor` applications. This fixes
the second application's failed instance synthesis without changing the local
finite-projective condition. All ten declarations and six public imports remain.

The source is the current main-20261015 blueprint, sec-six-functors-basics,
sk-prop-sf-pf-reduction/def-weil-site-perfect-complex.md, order 2225. The archived
1881 references are historical. Its four coefficient-stage clauses are retained,
as are both legacy and intrinsic rational/common-stage interfaces.

Change record: `coord/changes/G4-site-perfect-single-functor-category.md`.

## Proved and sorry left

This is a zero-hole definition repair: 0 existing sorries, 0 closed, 0 added,
0 remaining, and 0 split off. There are no theorem holes to enumerate.
`IsRationalFiniteProjectiveTerm` is restored as a concrete predicate, with the
same existential rank, localized retraction arrows, and splitting equation.
The untouched archive reproduces the failed `Quiver` synthesis at line 122
in 3.7 s. The repaired full module compiles remotely in 4.2 s with no errors or
warnings. The other nine declarations are unchanged. No new theorem or axiom is introduced.

## No longer needed

None. All public imports, all declarations, and all DAG statement dependencies
are preserved. No module or node is withdrawn. The item has zero live importers
because of quarantine, but its archived consumers remain needed.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because the upstream sync quarantined a genuine
elaboration error; it is not unused mathematics. The archive fails at the
second untyped single-functor category. Explicit category arguments repair the
inference problem while retaining the actual coefficient ring and module size.

The live-only downstream tool reports zero users, so consumer inspection also
included quarantine: twelve direct archived importers, with HomFiniteProjective
using the repaired predicate directly and the other consumers using its
site-perfect wrappers. No consumer signatures or proofs need adaptation.
No DAG statement or route changes are required for an elaboration-only repair.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
