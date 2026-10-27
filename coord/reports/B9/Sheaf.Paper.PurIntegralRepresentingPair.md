## What changed

Separated the unchanged coordinate representing-pair interfaces through Family into
`Sheaf.Paper.PurIntegralRepresentingPairData`, publicly reexported by the original
module. Added separate statements for the coordinate-family construction and the
fixed support-presentation compatibility with actual alpha. The parent constructs
its published linear Hom equivalences explicitly by precomposition and proves
naturality and both trace formulas from those coordinate data.

The interface move is recorded in
`coord/changes/B9-pur-representing-pair-interface.md`. PublishedFamily remains
in its original module. No existing signature,
structure field, definition body or target statement changes.

## Proved and sorry left

The original hole is
`WeilConjectures.PurIntegralRepresentingPair.reconstructedRepresentingPair`.
Its assembly is now an explicit construction from the coordinate-family and alpha
lemmas. One new hole remains in
`WeilConjectures.PurIntegralRepresentingPair.coordinateRepresentingFamily`
(node `lem-pur-coordinate-representing-family`). Its complete proof plan is in
its docstring and node. No definition has a hole. The abstract categorical identity
and its geometric specialization
`WeilConjectures.PurIntegralRepresentingPair.supportPresentation_alpha`, the
coordinate interface and the coordinate theorem all compile. The parent assembly
compiles without errors or warnings. One original
hole is closed and one coordinate-construction hole is added. The parent proof
constructs the linear Hom maps and proves all five naturality/trace fields; the
new hole is strictly the coordinate part of the argument.
The unchanged consumer `Sheaf.Paper.ReconstructedPairRefinementCoherence` also
compiles against the sandbox modules, without errors or warnings.

This is a decomposition: one original hole closed and one new hole added, net zero;
no claim of a net reduction of one sorry is made.

## No longer needed

No mathematical dependency is pruned: the coordinate construction retains the
original seven-step argument and all nine declared proof dependencies. The four
proof-only imports in the original file move to the coordinate-construction file.
The interface module imports only what its statements and constructions require;
its redundant direct imports of CompactSupportCondensedRealization,
BrownTowerFiniteSiteComparison and IntegralExceptionalInverseImage are provided
publicly by PurIntegralSupportComparison. These modules remain needed transitively.
No module is withdrawn. The unit route of sk-thm-purity-transport stays unchanged.

## Where the brief, the DAG or earlier work was wrong

Repair of approved head `478450ea137` (reviewer C-47845): the landing failed
because the reviewer fix used the repository basename instead of the loader's
change-record alias. The record stays at
`coord/changes/B9-pur-representing-pair-interface.md`; a reviewer override must
be named `B9-pur-representing-pair-interface.change.md`. This mapping is now
explicit in the record itself. No mathematical correction was requested. The
current-source comparison again preserves all 19 signatures and all 18 non-theorem
bodies; all four node attachments and dependency unions match. The current consumers are unchanged: ReconstructedPairRefinementCoherence is
now held by Z9, and restored PurRepresentingPairFiniteScalar is held by V6. The retained packet is recompiled
against the current published server build: all four packet modules and both
unchanged consumers compile with no diagnostics using `LCOMPILE_NO_LOCAL=1`.
`deliver3.py` rebuilds its commit on freshly fetched sheaf-dag.

No mathematical statement was corrected. The previous single hole bundled the
coordinate construction with the transport to the published support functor. The
new modules expose those two separate tasks. Exact equality of arbitrary system
maps is never inferred from level evaluations; evaluations detect isomorphisms,
and common-degree cohomology detects the stipulated concentrated-system squares.

## New nodes

`def-pur-integral-representing-pair-data` carries the existing interfaces extracted
verbatim, not a second definition. Its Lean attachment records Family and
the accompanying declarations remain under their original namespace.

`lem-pur-coordinate-representing-family` is the coordinate part of the integral
Hom display, before any transport to published support or published alpha. It
retains the actual counit and finite-evaluation normalizations and family squares.

`lem-pur-support-presentation-alpha` is solely the compatibility equation between
the fixed support presentation and the two actual reduction counits. Its proof is
naturality and the triangle identity, with no hypothesis of a representing family.

All new nodes use the current blueprint integral-adjunction Hom display and
unit/counit paragraph. Searches were run through LeanSearch, Loogle, LeanFinder,
and grep; Mathlib provides categorical tools, not these geometric conclusions.
Edge checks include identity support presentation, zero supplied systems, the first
finite level (index zero means exponent one), and the distinction between
conservative evaluations and faithful evaluation on concentrated systems.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
