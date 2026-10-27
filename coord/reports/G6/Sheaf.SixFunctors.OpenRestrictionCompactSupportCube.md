## What changed

Preserved the statement of AlgebraicGeometry.Etale.openRestrictionCompactSupport_cube.
Factored the geometric argument into the calculation with literal base-changed
compactifications and naturality of the support comparison in the compactifications.
OpenSupportCompactificationModel exposes the supplied-compactification version of the
existing graph/open comparison and the raw compactification exchange as constructed
isomorphisms. Neither definition chooses data from an existence theorem.

The main proof uses componentwise cancellation: expand each named exchange as raw
exchange followed by output comparison; apply the raw cube; move the output
comparisons through the support comparison and the open exchange by naturality;
cancel their inverses. The two new dependencies are proof imports only.

## Proved and sorry left

Closed the existing hole in
AlgebraicGeometry.Etale.openRestrictionCompactSupport_cube
(node lem-asd-open-restriction-compact-support-cube).

Added two holes, each in its own new module:

- AlgebraicGeometry.Etale.openSupportBaseChanged_cube
  (lem-asd-open-support-base-changed-cube): the calculation with literal base-changed
  output compactifications, without changing to chosen output models.
- AlgebraicGeometry.Etale.openSupportCompactificationIso_naturality
  (lem-asd-open-support-compactification-naturality): the comparison square when the
  two compactifications in an open-support comparison change, with no external
  base-change square.

This is a decomposition: one existing hole closed, two added, net minus one.
The item module has zero remaining holes. The new definitions have zero holes.
All four modules compiled through lcompile.py. The final item compile completed
without warnings in 13.8 seconds; the supporting modules compiled in 33.5 to
36.2 seconds. The original theorem signature was checked byte-for-byte unchanged.

## No longer needed

No imports were removed and no modules or nodes are pruned. The original geometric
proof dependencies remain needed below the two new obligations. They are no longer
direct proof dependencies of the item because its assembly uses the two new equations.
The general Noetherian compact-support formalism was inspected but is not imported:
its hypotheses do not cover the arbitrary schemes and arbitrary opens in this item.

## Where the brief, the DAG or earlier work was wrong

The listed geometric dependencies construct the component isomorphisms but do not
state their compatibility with the graph-defined support comparison. In particular,
an existence/composition isomorphism alone does not identify the specified map with
common-refinement comparison. The missing naturality equation is separated from the
calculation in base-changed models. Neither obligation is an objectwise renaming of
the original theorem: their combination requires explicit factorization, naturality,
and cancellation in the main proof.

The original signature and all existing definitions are unchanged. Empty schemes,
empty opens and the zero coefficient ring are covered by the same transformation
identities; no smoothness, boundedness or coefficient invertibility was introduced.

## New nodes

- def-asd-open-support-compactification-model records the actual constructed
  supplied-model comparison and raw exchange isomorphism.
- lem-asd-open-support-base-changed-cube records the geometric calculation before
  changing output compactifications. It has no quasi-compactness requirements.
- lem-asd-open-support-compactification-naturality records naturality of the open
  support comparison under common-refinement comparison, requiring quasi-compactness
  only where the existing common-refinement isomorphism needs it.

All three follow coherence (i) of prop-asd-smooth-base-change, retaining the existing
unit route. Searches used LeanSearch, Lean Finder, Loogle and Mathlib grep, plus repository
searches for the actual graph, exchange, comparison and cube declarations. No
existing statement or definition was repaired, so no change record is needed.

Preflight metadata repair: the definition node now attaches the primary definition
signature alone and lists both declarations in lean.declarations. All three new
nodes also record the actual LeanSearch query, in addition to Lean Finder, Loogle
and grep. The attribute commands added to the item are explicitly local proof
transparency settings: they change no imported declaration, signature or visibility.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
