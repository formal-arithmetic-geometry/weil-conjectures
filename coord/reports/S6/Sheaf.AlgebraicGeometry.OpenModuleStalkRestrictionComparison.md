## What changed

Completed the queued retirement of Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison.
The source twin constructs Scheme.openModuleStalkRestrictionComparison with exactly the
natural-isomorphism type previously wrapped by the Sheaf Nonempty theorem. Both remaining
consumers now import that twin and use its construction directly. The duplicate Sheaf module
is withdrawn using deleted.txt. The comparison node now records the source definition; the
transport node's first proof step names the construction actually used.

Change record: coord/changes/retire-open-module-stalk-restriction-comparison.md.
The two adapted consumer modules were unclaimed. Existing signatures, visibility and
public imports are unchanged; no source-library file or target statement is changed.

## Proved and sorry left

This is a retirement item with zero original holes, not a new proof or decomposition.
Holes closed: none (0 of 0). Holes added: none (0). Split off: none (0).
No sorry remains in either delivered consumer. The withdrawn comparison and its six private
supporting declarations were already proved; the source twin retains the complete construction.

Validation: the original assigned module compiled before retirement. Both adapted consumers
compiled through lcompile.py --all in import order (4.0 s and 33.9 s), with no warnings.
The delivery tool runs the axiom probes and preflight next. The comparison has no finiteness hypotheses, handles V=W, and x in V excludes the
empty-open case. Using the explicit isomorphism changes no existential conclusion.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison.
Removed its imports from Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport and
Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink; each now imports the source twin.
The duplicate six private helpers and Nonempty wrapper are unnecessary. No mathematical node
is deleted: lem-sc-open-module-stalk-restriction-comparison is realized by the source
construction. Its existing dependencies and the unit route are retained. No other module or
node is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an obligation that had already been proved. The actual
queue row is a zero-hole retirement item. The API difference is only that the source returns
the natural isomorphism itself rather than Nonempty of it. The inventory's four consumers
have become two live Sheaf consumers; the other two have already been retired.
Library search found the exact source construction. Mathlib search with msearch.py leanfinder
returned the additive restrictStalkNatIso and germ formulas; loogle and grep returned no exact
match. Direct rg inspection of both library roots found the stronger constructive source API.
The full source proof follows the existing three-step germ, scalar-composition and functor
comparison argument, so the mathematical proof route has not changed.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
