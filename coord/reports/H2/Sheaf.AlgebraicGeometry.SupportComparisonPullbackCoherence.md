## What changed

Proved `AlgebraicGeometry.ProEtale.supportSiteComparison_pullback_coherent` by specializing
`AlgebraicGeometry.ProEtale.comparison_pullback_coherent`, already proved in
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`. The theorem retains sets, abelian
groups, every finite fixed coefficient ring, identities, arbitrary composites, and the
supplied Cartesian square with its commutativity transport.

`supportSiteComparisonPullbackCoherent` now abbreviates `ComparisonPullbackCoherent`.
The support-prefixed functors, adjunctions, and canonical isomorphisms keep their bodies
and signatures. The reused predicate has exactly the original equations: its square
clause unfolds through `ComparisonSquareComponent` and `comparisonSquareData`. Its module
is a public import because the predicate body uses it. Direct proof transfer against the
expanded old predicate and a simp-only transfer exceeded the 60-second file limit in the
previous attempt; the compact predicate version compiles in 3.9 seconds in this session.
The original baseline also compiles, so this is a conversion-cost repair.

The definition-change record is
`coord/changes/H2-support-comparison-pullback-coherent-reuse.md`. Its refreshed inventory
lists all 1317 downstream modules and their current holders; there are 86 direct consumers.
No consumer requires adaptation. The source index's comment-stripped search finds no code
use of either changed name outside the item. A whole-source search additionally finds
only a docstring mention in `SupportComparisonBoundary`.

The item node retains the four mathematical steps and records reuse of their existing
Lean proof. Its statement, dependency sets, and unit route are unchanged. The obsolete
note about incompatible import families is corrected.

Validation in this session: the item compiles without warnings in 3.9 seconds, and the
import-direction check permits its new import. Seven generic `rfl` checks identify the
etale/pro-etale identity, composition, and chosen-square isomorphisms and the coefficient
pullback comparison with the existing ones. The checks compile against the identical
sandbox item. `#print axioms` of both coherence theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The previous attempt checked its then-current 17 direct consumers: 16 compiled, including
`SpDirectImageEtaleMate`. `LisseCompletedSystemComparison` exceeded 60 seconds against both
the change and the unchanged published library; no adaptation is made for that baseline
timeout. `FiniteRingCompactSupportProjectionMap` had an existing long-line warning.

## Proved and sorry left

Closed one of the item's one holes:
`AlgebraicGeometry.ProEtale.supportSiteComparison_pullback_coherent`
(node `lem-weil-pbc-comparison-pullback`). No holes remain in the item. No holes added,
no split-offs, and no new nodes. The completed theorem has no transitive `sorryAx`.
This reuses an already proved theorem; it is not a decomposition.

## No longer needed

Removed two proof-only imports:
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
The reused proof and existing public imports supply everything the item needs.
All pre-existing public imports remain for consumer compatibility. No modules are
withdrawn and no mathematical node dependency is pruned: the existing proof implements
the same four steps using the same constructions and adjunctions. A second support-prefixed
mate/coherence calculation is unnecessary.

## Where the brief, the DAG or earlier work was wrong

The old Lean attachment note says the ordinary and finite-coefficient inverse-image APIs
cannot coexist because of duplicate declarations. The landed compatibility re-export
repair in `coord/changes/H2-proetale-duplicate-exports.md` resolved this; the current imports
compile together. The U2 square API refactor documented in
`coord/changes/U2-comparison-pullback-coherence-square-api.md` already provides a compact
representation of the identical unprefixed predicate. This delivery reuses that interface.

The predicate change preserves the mathematical statement but is an interface change
submitted with its change record for independent review, including target meanings.
No target declaration is edited.

Earlier attempts failed in delivery setup: one was killed with exit 137 and another
reported `git checkout -q --detach origin/sheaf-dag` timing out after 600 seconds.
The first dry run of this resumed session waited for worktree capacity and its process
was no longer present after the provider interruption; its terminal result was unavailable.
No push was requested by those dry runs. The required dry run has been restarted with
its output retained under scratchpad.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
