## What changed

The statement of `systemPullbackCompositorEvaluation` is unchanged. Its proof reduces the
ordinary-to-derived part to the proved exact-square composition theorem. A private localization
calculation identifies `c.pullComp` with the exact localization of `c.ordinaryPull`, using its
`pullComp_model` certificate. The ordinary evaluation square then descends through the specified
cochain normalization, and a generic categorical calculation gives the requested inverse
orientation.

The remaining ordinary module-sheaf square is stated in the new proof dependency
`Sheaf.Paper.OrdinarySystemPullbackCompositorEvaluation`. It is steps 1 and 2 of the original
argument, with no complexes, derived objects or localization. Thus the decomposition removes the
localization and inverse-orientation work from the remaining task; it does not merely reverse or
rename the assigned derived identity.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.IntegralSystemRealization.systemPullbackCompositorEvaluation` from the ordinary
square. Added one hole:
`WeilConjectures.IntegralSystemRealization.ordinarySystemPullbackCompositorEvaluation`
(node `lem-pur-ordinary-system-pullback-compositor-evaluation`). This is a decomposition: one
original hole closed, one simpler ordinary hole added, net zero. The item module has zero holes;
the delivery has one hole. All private helpers have complete proofs. Remote `lcompile.py` compiled the item in
20.7 seconds and compiled the new ordinary module; the final style-only edits replace `letI`
with `let` as requested by the linter.

## No longer needed

No existing public import or declaration is removed. No existing node or module is declared
unnecessary. `lem-pur-ordinary-pullback-composition-evaluation` remains on the new ordinary node's
proof route; it is no longer a direct dependency of the derived-localization argument.

The generic proved tool `lem-pod-derived-exact-square-composition` replaces the need to reproduce
its cochain pasting and essential-surjectivity argument in this item. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or the DAG plan. The original plan's ordinary
and localization steps had not yet been separated into usable declarations. The existing generic
exact-square composition theorem handles the latter step. The remaining ordinary normalization
has its own theorem and complete proof in words.

## New nodes

`lem-pur-ordinary-system-pullback-compositor-evaluation` states the ordinary module-sheaf
composition square for the specified section-normalized compositor and the unit-normalized
intrinsic finite pullback comparisons. It realizes the first two steps of the original node.
Its source is Stacks Tag 03D8, specialized to the existing ordinary adjunction normalizations.
LeanSearch, LeanFinder, Loogle, local source searches, and a Mathlib source search found generic
mate and pullback-composition tools but no statement with these specified comparison maps.
No existing public interface was changed, so no consumer adaptation or change record is needed.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
