## What changed

Proved `CategoryTheory.RingedSitePoint.nonempty` in
`Sheaf.CategoryTheory.Sites.RingedSitePoint` by explicitly transporting the operations
along the inverse-image functor's inverse product and terminal comparisons. The ring
carrier is the given inverse image of the underlying ring sheaf; module carriers are
likewise the given inverse images. All algebraic laws, linearity, functoriality,
naturality, additivity and the seven operation-graph fields are proved. No object is
selected from an unproved existence statement.

Added only private constructions and proved helpers, plus the proof import
`Mathlib.CategoryTheory.Sites.CartesianMonoidal`. The original public imports,
structure and theorem signatures remain unchanged. Updated the node's formerly empty
proof plan to describe the implemented calculations; no new dependencies are needed.

Validation: remote single-file compilation succeeded without warnings in 9.1 seconds.
The unchanged direct consumer `Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion`
also compiled successfully against this module in 2.0 seconds. `#print axioms CategoryTheory.RingedSitePoint.nonempty`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed 1 of 1 original holes: `CategoryTheory.RingedSitePoint.nonempty`
(node `def-sfb-ringed-site-point`). Added 0 holes; split off 0 statements.
No sorry remains in the module or any delivered helper. This is a full proof.

## No longer needed

No original imports, DAG nodes or modules were pruned. There were no stated proof
dependencies to bypass. A redundant experimental private import of
`Mathlib.CategoryTheory.Monoidal.Types.Basic` was removed; the CartesianMonoidal
import already provides it. The source library's internal-ring transport was searched
and read, but is not needed: simultaneous generalized representatives give both ring
and module laws directly, with the original independent universes.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The existing node had an empty `proof` and no
`proof_deps`; the theorem docstring supplied the intended argument, which is now
implemented and recorded in five calculation steps. The unit route is unchanged.
No definition repair, consumer adaptation or new node was necessary. The preflight
classifier conservatively requires a change record for the added namespace commands;
`coord/changes/J1-ringed-site-point-private-proof-scopes.md` records their scope and
the unchanged consumer interfaces.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
