## What changed

Proved `WeilConjectures.IntegralSystemRealization.FiniteCoordinates.rhsCoreBridgeCancellation`
without changing its statement. The private proved helper `insertBridgeFactors` performs the
calculation for arbitrary categories, functors, two isomorphisms, and unchanged outer
morphisms. The main theorem applies it directly to the push and shriek bridge components.
This avoids unfolding the two definitionally equal coefficient presentations inside
rewriting tactics.

Replaced the public import of `Sheaf.Paper.SystemFiniteRefinementMateCanonical` with the
defining module `Sheaf.SixFunctors.IntegralCompactificationRealizationData`, which supplies
`Realizations`. Removed the redundant private import of
`Sheaf.SixFunctors.AmbientProperOpenCalculus`; the finite-coordinate module already exports
it. Updated the item's DAG proof and proof dependencies to the formal isomorphism
cancellation actually used. No other module or node is changed.

## Proved and sorry left

Closed 1 original hole, in
`WeilConjectures.IntegralSystemRealization.FiniteCoordinates.rhsCoreBridgeCancellation`
(node `lem-sf-system-finite-refinement-mate-rhs-normalization-bridge-cancellation`).
Added 0 holes and split off 0 statements. The item has 0 remaining `sorry` declarations.
The private helper is fully proved with `Functor.map_comp`, `Functor.map_comp_assoc`,
`Category.assoc`, `Iso.hom_inv_id`, `Functor.map_id`, and `Category.id_comp`.

The first successful proof compile was clean in 20.5 seconds. The final import set
compiled cleanly in 47.6 seconds, followed by the unchanged sole direct importer
`Sheaf.Paper.SystemFiniteRefinementMateRhsCore` in 16.6 seconds, one file at a time
in import order. The interrupted command completed with exit code 0; its saved result
was read before any resubmission. The unchanged consumer copy was then removed from
the delivery sandbox. Delivery additionally runs the declaration/axiom probe and
related-module checks.

## No longer needed

Removed the item's import edge to `Sheaf.Paper.SystemFiniteRefinementMateCanonical`:
`canonicalEvaluation` and its node `lem-sf-system-finite-refinement-mate-coordinates`
are not used in this bridge cancellation. The defining realization-data module is
imported directly. The canonical evaluation theorem remains used by other modules,
so this does not withdraw or globally prune its module.

Removed the redundant explicit import of
`Sheaf.SixFunctors.AmbientProperOpenCalculus`; it remains a transitive statement dependency.
The planned proof dependency `def-sf-system-finite-evaluation-coordinates` is needed
for the statement's coordinate isomorphisms, but none of its properties or definitions
needs expansion in the proof. It remains in `stmt_deps` and is removed from `proof_deps`.
No DAG node or module is withdrawn; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan proposed expanding finite-coordinate definitions and applying
mate and coefficient-equivalence triangle identities. The displayed statement only
inserts an evaluated push bridge, the direct image of a shriek bridge, and their
inverses into an unchanged composite. Functoriality and isomorphism cancellation
already prove exactly that statement, including identity refinements, zero objects,
and empty opens. The generic helper needs no geometric hypotheses.

The current server queue classified this item as a proof item with one hole; there
was no assigned rework or build-error record. No statement repair was necessary.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SystemFiniteRefinementMateRhsBridgeCancellation": "0a90901e45b1e78eebf8157e04d2a2e72e58e1a6"}, "results": {"Sheaf.Paper.SystemFiniteRefinementMateRhsCore": {"hash": "3775b3b45a6ed5083b0a133f1e6211f47226f0e1", "status": "OK"}}, "seconds": 187, "time": "2026-10-28T14:19:15+0800", "transitive": 0, "version": 1}
```

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
