## What changed

Completed the assigned retirement row
`retire:Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData` in
`coord/retire-items.tsv`. Withdrawn the proved Sheaf duplicate through
`deleted.txt` and redirected node
`lem-sc-proj-twist-finite-localization-data` to the existing upstream theorem
`AlgebraicGeometry.Proj.twist_finiteLocalization_data` in
`WeilConjectures.AlgebraicGeometry.ProjTwistFiniteLocalizationData`.
The node's Lean record contains the upstream signature verbatim and explains
the retirement. No source-library file, target, mathematical statement,
dependency edge, proof route, or unit step changes.

Change record:
`coord/changes/C4-retire-proj-twist-finite-localization-data.md`.

The theorem signatures agree after renaming the unused existential span-proof
binder `hspan` to `_`; the theorem proof bodies agree verbatim. Remaining file
differences are header attribution and a local unused-variable lint option.
A temporary Lean example with the original full Sheaf signature is proved by
applying the upstream theorem. The example compiles with the original local
lint setting. A separate temporary axiom probe imports the upstream theorem
and its parent and checks both declarations: they use only `propext`,
`Classical.choice`, and `Quot.sound`. Both temporary probes were removed.

`tools/downstream.py` reports zero downstream modules of the Sheaf duplicate.
A source search across both library roots and `quarantine/` finds no imports
of it. The retirement inventory's former consumer
`Sheaf.AlgebraicGeometry.ProjTwistFractionDescent` is already absent; its node
points at `WeilConjectures.AlgebraicGeometry.ProjTwistFractionDescent`, which
already imports the upstream finite-localization theorem. Its proof dependency
on the mathematical node remains satisfied. No consumer edits are needed.
The upstream theorem and parent have no nonempty Sheaf/upstream twin pair in
their source import closures. The inventory's prerequisite retirements of
`ProjTwistFiniteLocalRepresentatives` and `ProjTwistFiniteValues` are complete.

Searches via `msearch.py` covered LeanFinder, Loogle and Mathlib grep.
LeanFinder found Proj structure-sheaf fraction infrastructure; Loogle found
homogeneous localizations; grep found localization and span lemmas.
Direct library search found the exact proved upstream theorem, which is
retained instead of constructing another proof. The unit
`sk-thm-picard-duality` has no realized step at this level, and its route stays.

## Proved and sorry left

Zero of zero holes closed; zero holes added; zero statements split off.
The assigned module and its upstream twin already contain no `sorry`.
No new theorem proof is claimed: this delivery retires a proved duplicate.
The retained declaration is
`AlgebraicGeometry.Proj.twist_finiteLocalization_data`;
its parent `AlgebraicGeometry.Proj.twist_fraction_descent` remains proved.
There are no remaining holes in any delivered Lean content.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData`, including its
private helper `exists_unit_of_span_top` and duplicate theorem proof. Its
imports are no longer compiled through that copy. No current import line
needs removal: the former parent already uses the upstream twin.
No mathematical node, dependency, lemma or unit step is pruned. In particular,
`lem-sc-proj-twist-finite-localization-data` is retained, attached upstream,
and still supplies the parent's existing argument. No other module is
withdrawn, and no upstream declaration is removed or weakened.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a repeatedly split open proof. The current
retirement inventory assigns a proved duplicate with zero holes instead.
Its stale consumer column lists an already-retired Sheaf parent. The actual
repair is withdrawal of the duplicate and redirection of its Lean attachment,
with the existing upstream parent and all mathematical dependencies retained.
The DIFFERENT classification reflects nonmathematical file differences and
an unused binder name. No statement is disputed, no new node is created,
and no forced adaptation is needed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
