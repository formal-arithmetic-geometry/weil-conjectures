## What changed

Restored WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
at its live Lean path, byte for byte from the quarantine path named by coord/rework.tsv.
The source module had been removed after a cluster restoration was reverted; this delivery
restores the missing comparison and exchange constructions with every existing declaration,
public import, attribute and proof preserved. The original compile already succeeds against
the current dependencies (3.3 seconds). No extra proof refactoring was needed or introduced.

Corrected the Lean attachment of lem-weil-pbc-condensed-basechange-counit: the actual signature
uses bundled Over objects, X.left and k inferred from sq. The old attachment passed k explicitly.
The node statement and dependency route remain unchanged. The restricted pushforward and its
adjunction retain the existing IsFinitenessCoefficient section assumption.

Reviewed the comparison unit and its definition node, the counit node, and the existing generic
Adjunction.squareExchange API. The comparison remains the two composition isomorphisms with
equality transport in between. The three base-change steps remain exactly the unit-square-counit
construction; boundedConstructibleBaseChange_adjunct follows from squareExchange_map_counit.
Searches used leanfinder (generic mate and square results), loogle (homEquiv_counit), and local
source searches (squareExchange and exchangeRight). No alternative route or new lemma was needed.

Compiled the unchanged archived consumer Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
against the restored source in the sandbox overlay (2.4 seconds, no errors or warnings). This
consumer is retained only in scratchpad for review, not included among delivered Lean modules.
The change record lists live and quarantined direct importers and their current claim holders.

Change record: coord/changes/C3-restore-bounded-base-change-morphism-defs.md.

## Proved and sorry left

This is a zero-hole rework/restoration: 0 original sorry proofs, 0 closed, 0 added, 0 remaining,
and 0 split off. There are no declaration names to list as remaining holes in the item or added
modules. No claim is made to prove already proved declarations again.
All existing proofs are preserved, including boundedConstructiblePullbackSquareComparison_app,
boundedConstructibleBaseChange_eq_unit_square_counit,
boundedConstructibleBaseChange_eq_squareExchange, boundedConstructibleBaseChange_adjunct,
and boundedConstructibleBaseChange_eq_exchangeRight. Their imported finiteness theory retains
its pre-existing dependencies; restoration is not a claim that those dependencies are hole-free.

## No longer needed

None. No imports, declarations, modules, DAG dependencies or unit steps are removed.
Both DAG attachments and all dependencies of the quarantined source are preserved. The archived
module is not withdrawn and is not replaced by an empty module.

## Where the brief, the DAG or earlier work was wrong

The item is an explicitly listed rework with zero holes. Its live source is absent, while the
assigned archive compiles after the intervening dependency repairs; no compiler failure remains
inside that archived source. Restoring it is the repair, without claiming a new mathematical proof.
The counit node's Lean attachment was stale after the upstream migration to Over objects and
implicit k; corrected in this delivery. No target signature, natural-language statement or route
was changed. The source-library boundary calls for exact archive preservation here.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
