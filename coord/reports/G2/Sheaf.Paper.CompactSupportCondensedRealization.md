## What changed

`Sheaf.Paper.CompactSupportCondensedRealization.omegaProjection_isIso` now applies the
proper coefficient comparison to the actual extension by zero of its input. The existing
open-extension preservation theorem supplies bounded constructibility; the intermediate
scheme is noetherian because it is proper over the finite-type base. Expanding the defined
`condensedProjection` and `pasteScalar` then composes this proper isomorphism with the
canonical open scalar isomorphism and the functor associators.

The new proof import is `Sheaf.Paper.OmegaProperCoefficientProjection`. It isolates the
proper factor, with no compactification or open map, in
`omegaProperCoefficientProjection_isIso`. Its source and complete proof in words describe
finite coefficient complexes with one lower bound, finite-stage comparisons, continuity
on each homology degree, and identification with the specified counit transpose. Public
statements, definitions, attributes and public imports of the original module are unchanged.

Validation: the clean two-module import-order compile passed without warnings. Both
requested files were accepted under the service's 60-second Lean execution limit. The
displayed service totals (66.6 and 102.9 seconds) include setup and cache work, which is
separate from the enforced Lean execution limit.

## Proved and sorry left

This is a decomposition: **one upper hole closed, one lower hole added, net zero holes**.
The completed Lean combination closes
`WeilConjectures.CompactSupportCondensedRealization.omegaProjection_isIso`.
No claim is made that the proper filtered-continuity argument has been formalized.

The four original holes left, all attached to
`lem-pur-compact-support-condensed-realization`, are:

- `WeilConjectures.CompactSupportCondensedRealization.systemRefinement_id`;
- `WeilConjectures.CompactSupportCondensedRealization.systemRefinement_comp`;
- `WeilConjectures.CompactSupportCondensedRealization.omegaRefinement_isIso`;
- `WeilConjectures.compactSupport_condensedRealization`.

The one new hole is
`WeilConjectures.CompactSupportCondensedRealization.omegaProperCoefficientProjection_isIso`,
attached to `lem-pur-omega-proper-coefficient-projection` in the new module
`Sheaf.Paper.OmegaProperCoefficientProjection`. Its proof is exactly `by sorry`.
There are four holes in the item and one in the new module; no definition has a hole.

## No longer needed

No existing import, declaration, module or node is withdrawn or pruned. The old direct
coefficient-presentation and continuity uses of the closure-projection step move into
the new proper-factor node. They remain necessary there; they are not advertised as
pruned work. All other steps and the unit route remain in place.

## Where the brief, the DAG or earlier work was wrong

No statement error was established. The available ambient unbounded algebraic-closure
pushforward instance explicitly assumes preservation of all coproducts. Properness alone
does not supply that premise, so it cannot discharge this bounded-input comparison.
The new node instead retains the original common-lower-bound continuity argument.

The existing source refinement isomorphism requires a cartesian square. The item's
ordinary refinements need not have cartesian open squares, so that result does not directly
settle `omegaRefinement_isIso`. The original general refinement statement is preserved.
Attempts to specialize generic semilinear unit and pasting laws also encountered expensive
conversion between the two coefficient-system presentations. These scratch attempts are
not part of the delivery, and no additional hole is claimed closed by them.

## New nodes

`lem-pur-omega-proper-coefficient-projection` is the proper factor of the original
closure-projection argument. It states invertibility of `condensedPushScalar` for a
proper map and a bounded constructible finite-coefficient input, before any open extension
or compactification. The original theorem still has to establish that its extended input
meets this premise and then paste the open comparison. Thus the new statement is a part
of the argument, not a renamed compact-support assertion. The node records the source,
five proof steps and four Mathlib searches covering the three required kinds. The zero input
and empty schemes give zero comparisons; for an identity proper map the coefficient adjunction triangles give
the unit comparison. No nonempty, nonzero, or stronger unbounded-continuity assumption
is introduced. There are no definition changes and no change record is required.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
