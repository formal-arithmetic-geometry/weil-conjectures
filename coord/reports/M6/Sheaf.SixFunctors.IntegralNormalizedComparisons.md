## What changed

Replaced the hole in `Sheaf.SixFunctors.IntegralNormalizedComparisons` by the restriction
of `compactification_coherence_cocycle` along the equality Loc(Dctf) = Loc(Dbc) for O_E.
Whiskering proves identity and cocycle. For an arbitrary boundary refinement, choose a
dense refinement of its source; the canonical normalization and composition law cancel
its invertible component. This identifies the chosen comparison with the refinement
isomorphism supplied by the new single-refinement normalization lemma.

The new module `Sheaf.SixFunctors.IntegralBoundaryRefinementNormalization` states the
remaining calculation for one refinement and one complex in Loc(Dctf): invertibility of the canonical
open-extension map, its total-adjunction normalization, and identification of the inverse
pushed-forward isomorphism with the canonical refinement component. It asserts no family,
identity or cocycle. Its proof and source are recorded in its docstring and new node.
The caller proves the extra Loc(Dctf) membership from the equality of localizing closures.
Existing public statements and definitions are unchanged. No source-library module changes.

Validation: both modules typechecked. The profiled single-file check of the item took
36.4 seconds; the final packet removes its temporary profiler options and fixes the
reported style warnings. The delivery tools run the final compile and preflight checks.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.normalizedComparisons`
(node `lem-sfb-total-derived-normalized-comparisons`) by a complete proof from the
canonical coherence family and the single-refinement lemma.

Added one hole, exactly the named public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.integral_boundaryRefinement_normalization`
(node `lem-sfb-boundary-refinement-total-normalization`). There are zero holes in the item
module and one in the new module. This is a decomposition: one upper hole closed, one
strictly smaller hole added, net zero holes closed. All private helpers are proved.

## No longer needed

No existing node or module is withdrawn. The redundant direct proof import of
`CompactificationRefinementLocalizing` in the retained candidate is removed; the refinement
node remains needed transitively by the new lemma. The proof still needs canonical coherence,
localizing closure equality, common dense refinement, and the refinement normalization
route. The large unverified transport proof retained by the earlier attempt is replaced
by the explicitly documented remaining lemma, rather than reported as proved.

## Where the brief, the DAG or earlier work was wrong

The retained candidate had not compiled: missing mirrored dependencies initially hid
elaboration and kernel failures in transport calculations. A remote compile exposed them.
The current packet records the unresolved single-refinement calculation honestly. It does
not replace the comparison-family obligation with the same obligation under another name.
Empty opens, zero complexes, and non-dense compactifications are allowed: density is only
required of the auxiliary refinement used for cancellation. The new lemma's proof explains
how dense refinements remove the density assumption for its canonical map.

## New nodes

`lem-sfb-boundary-refinement-total-normalization`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-boundary-refinement-total-normalization.json`,
records the one-refinement total-adjunction normalization and inverse-component step of
the existing argument. Its statement is strictly a part of the original proof: the main
module still constructs the global family, proves its equations, restricts the localizing
category, and identifies every comparison by cancellation. No change record is needed,
since no existing statement or definition changes.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
