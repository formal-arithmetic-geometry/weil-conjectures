## What changed

Reduced `AlgebraicGeometry.ProEtale.reductionExceptional_isIso`, with its exact original
signature, to the separate source realization and chart counit calculations. The assigned module now
constructs the four constructible preservation witnesses, transports ordinary etale
exceptional adjunctions, lifts the fixed compact-support coefficient comparison, takes
its inverse mate, and proves the counit identity and uniqueness. Its proof imports are
private imports of ReductionDirectImage and the three new mathematical lemmas.

`ReductionExceptionalRealization` states the single-ring adjunction and its realization,
including the actual compact-support counit equation, as a separate source obligation.
Its recorded proof uses ordinary constructible preservation and the finite-coefficient
comparison equivalence. The attempted complete construction repeatedly exceeded the
kernel limit despite abstract counit APIs and componentwise comparisons; the complete
combining proof uses this named statement. No definition chooses data from it.

`ReductionExceptionalConservativity` proves componentwise invertibility from the exact
chart equation. It chooses a common annihilator and the normalized ordinary P1 data,
uses the finite admissible coordinate cover, cancels the specified comparison
isomorphisms on each chart, and detects the vanishing cone on that cover.

The existing definitions and proved helpers preceding the main theorem are moved
verbatim to `ReductionExceptionalObjects`, and publicly reexported by the original
module. This breaks the otherwise unavoidable self-import in the separate source
lemmas. No definition, declaration signature, visibility, attribute or target meaning
changes. The change record lists all 249 recorded transitive consumers
(133 currently downstream, with earlier recorded consumers retained). No source-library
module is changed.

The return of head `22b4d1d4245` reports that reviewer C-22b4d passed the
mathematics, but the landing rejected a reviewer fix filename. The change record
is included at `coord/changes/K5-reduction-exceptional-interface-relocation.md`.
In the current `tools/batch_land.py`, the corresponding reviewer override filename
is `K5-reduction-exceptional-interface-relocation.change.md`; the returned plain
`.md` override filename is not recognized. The repository change-record filename
itself stays unchanged. This repair refreshes its consumer/holder table and records
the required override key, so any further reviewer edits can use the supported
landing interface. The relocated interface is still a byte-for-byte prefix of the
current original module. No mathematical edits were requested or introduced.
The delivery tool rebases the retained packet onto current sheaf-dag and recompiles
all five modules on the server before pushing.

## Proved and sorry left

Closed the original body of `AlgebraicGeometry.ProEtale.reductionExceptional_isIso`
(node `det-sp-reduction-exceptional`): one original hole.

Added exactly two holes:

- `AlgebraicGeometry.ProEtale.reductionExceptionalRealization_exists`
  (node `lem-sp-reduction-exceptional-realization`), the single-ring source
  Steps 3--4 adjunction and counit-preserving realization.
- `AlgebraicGeometry.ProEtale.reductionExceptional_chartEquation`
  (node `lem-sp-reduction-exceptional-chart`), the source Steps 5--12 chart
  calculation for already supplied adjunctions, realizations and a map satisfying
  the counit identity. It asserts neither adjunction existence nor uniqueness nor
  global invertibility.

This is a decomposition: one original hole closed, two added, net minus one.
The assigned theorem is completely proved from these two strictly separate parts
and the proved conservativity lemma. It is not a proof from hole-free foundations.
`AlgebraicGeometry.ProEtale.reductionExceptional_components_isIso` has a complete
proof from the stated dependencies. All private helpers are proved. No other sorry
is retained or added, and no definition contains a sorry.

## No longer needed

No existing mathematical module is withdrawn or globally pruned. The original public
imports remain verbatim in the publicly reexported objects
module. The main module now directly imports only Objects publicly, and privately
imports ReductionDirectImage (including its proved private preservation API),
ReductionExceptionalRealization, ReductionExceptionalConservativity,
ReductionExceptionalChart, and Mathlib.CategoryTheory.Adjunction.Mates.
All its former imports are supplied by the verbatim Objects reexport; the former
proof imports used only by relocated definitions are unnecessary in the main proof.

The main proof uses the new realization, chart and conservativity nodes instead of
listing every source chart step as its immediate proof dependency. The original
finite-Tor comparison and etale/pro-etale transfer work remains required by the
recorded proof of the realization lemma; the finite admissible cover and open-cover
detection are used by the proved conservativity lemma. The source P1 trace, sum counit, chart adjunction, scalar counit
transport and open exceptional locality remain necessary to the chart lemma and are
not claimed as pruned. No maintainer tool-use approval is added or reordered.

The realization node no longer cites the general pro-etale direct-image stability
package `det-thm-sf-ctf-stability-direct-images`. Its current dependency closure now
returns to the parent reduction theorem through tame-boundary purity and dualizing
support, so it cannot be an input here. The retained realization argument needs only
the already proved ordinary-etale finite-ring exceptional and compact-support
preservation APIs underlying `sk-prop-sf-rf-shriek-preservation`. Its proof step now
names that source precisely, preserving the original unit route. This removes an
unused broad citation; no global pruning of the stability module is claimed.

## Where the brief, the DAG or earlier work was wrong

The first repair preflight pushed nothing: it detected the newly cyclic broad
stability citation after rebasing. The realization node's preservation step was
reconciled with the ordinary source APIs actually used in its argument, and the
replacement dependency was checked for a return path to the parent; there is none.

No statement is disputed. The interface was housed in the same file as the theorem,
so a separate chart or realization lemma would otherwise import its own parent. The
verbatim objects-module relocation resolves this module-level issue without changing
any mathematical object. The source proof steps are retained as the realization,
chart-counit and local-to-global parts of the reduction. Zero rings, zero-dimensional
charts and empty covers are allowed: the proof uses invertible-exponent witnesses,
identity zero-coordinate towers and cone detection on the actual covering family.

The repair dispatcher reset the reference clock at 2026-10-25 20:29 UTC with `repair: true`.
The original attempt is delivered head `22b4d1d4245`; this retry retains its proof
work and two previously reviewed split statements. No additional hole was introduced
in the repair, and no budget metadata was changed by the worker.

## New nodes

`def-sp-reduction-exceptional-realization-objects` owns the relocated existing interface.
It has no new mathematical data. The existing affine-counit comparison objects node
is reattached to the objects module as well.

`lem-sp-reduction-exceptional-realization` is the retained single-ring existence and
counit-preserving realization statement (source Steps 3--4). It is unfinished.

`lem-sp-reduction-exceptional-chart` is the retained source chart-counit calculation
(source Steps 5--12), and is the second new unfinished theorem.

`lem-sp-reduction-exceptional-components-isIso` is the proved finite-cover
conservativity implication (source Step 13).

Change record: `coord/changes/K5-reduction-exceptional-interface-relocation.md`.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
