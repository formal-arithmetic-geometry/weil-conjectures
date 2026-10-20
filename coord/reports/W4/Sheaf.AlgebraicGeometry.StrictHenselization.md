## What changed

Retire the zero-hole copy Sheaf.AlgebraicGeometry.StrictHenselization, as requested
by coord/retire-items.tsv. Withdraw its module using deleted.txt. Repoint
node def-weil-pbc-strict-henselization-limit to the existing source-library module
WeilConjectures.AlgebraicGeometry.StrictHenselization, retaining its three recorded
declarations strictHenselizationRing, strictHenselizationScheme and
strictHenselization_properties.

All 31 current direct consumers import
WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension instead, preserving
public/private import visibility. Nine existing consumers use
strictHenselizationAffineDiagram instead of smallStrictHenselizationDiagram;
36 consumer modules change in total. The Lean attachment of
lem-sbc-pointed-etale-ring-colimit-base-map-naturality is refreshed to match
its definitionally identical adapted signature. The upstream extension provides the other
three declarations verbatim, so their call sites keep their names. The structural-flatness proof drops two unreachable fallback tactics after the
diagram replacement; its successful proof branches are unchanged. No upstream
file, target statement, theorem hypothesis, or mathematical proof argument is changed.
The consumer table and exact old/new interfaces are in
coord/changes/W4-strict-henselization-retirement.md.

## Proved and sorry left

This is a retirement repair with zero holes in the item: proved 0 of 0 sorries;
0 holes added and 0 split off. No sorry remains in the withdrawn item. Existing
consumer proof holes, where present, are unchanged. No theorem is claimed as a
new proof or decomposition.

Validation: all 36 adapted consumers and 25 unchanged intermediate modules
compiled remotely. Two unused fallback branches in the structural-flatness proof
were removed to clear the only warnings; separate reflexivity checks for the diagram, cocone
and comparison isomorphism, and an axiom audit of the upstream replacements. The three reflexivity checks
compiled in 2.8 seconds; the comparison isomorphism, cocone, colimit witness and
strictHenselization_properties use only propext, Classical.choice and Quot.sound.
The 25 unchanged intermediate source copies were removed after validation; their
compiled sandbox artifacts support consumer checking.

## No longer needed

The complete duplicate module Sheaf.AlgebraicGeometry.StrictHenselization is
withdrawn. No current library module imports it after the edits. Its definition
smallStrictHenselizationDiagram is replaced everywhere by the existing identical
strictHenselizationAffineDiagram. Its duplicate definitions
smallStrictHenselizationColimitIso, smallStrictHenselizationCocone and
isColimitSmallStrictHenselizationCocone are supplied by the upstream extension.

The removed module's five direct imports (Mathlib.AlgebraicGeometry.GammaSpecAdjunction,
Mathlib.Algebra.Category.Ring.Colimits,
WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization,
Mathlib.CategoryTheory.Filtered.Final and
WeilConjectures.AlgebraicGeometry.StrictHenselization) remain available as needed
through the upstream extension; no other mathematical dependency is pruned.
Preflight also required removing the unused private import
Sheaf.AlgebraicGeometry.LogSmoothDifferentialLocalFreeness from
LogSmoothDifferentialGenerators because it is listed in
coord/route-pivot-dropped-modules.txt. No declaration uses that import; the
existing theorem body is unchanged. No DAG node is removed. The node attachment now refers to the official source
construction and the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The first dry run reached preflight and was refused only because an existing
consumer privately imported the route-pivot dropped LogSmoothDifferentialLocalFreeness.
That unused import was removed; the source statement and existing hole remain unchanged.
The axiom-probe diagnostics reported timeouts on three existing large files;
normal file compilation passed, and the tool explicitly reruns these probes at merge.

The ordinary stage-3 brief says to prove holes, but this item is a zero-hole
retirement item. The retirement TSV says the twin lacks the three comparison and
cocone declarations; they have moved to
WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension. The remaining
small-diagram declaration is identical to strictHenselizationAffineDiagram.
Keeping the copy alongside the extension causes duplicate-name import failures,
already recorded for two quarantined consumers in coord/rework.tsv. The original
node's Lean attachment pointed to a Sheaf module re-exporting the base construction;
it now points directly to the adopted upstream definition.

The current blueprint source was read at
literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-sf-comparison/def-weil-pbc-strict-henselization-limit.md. The construction,
pointed-neighbourhood indexing and Spec/colimit interpretation are unchanged.
The unit's realized list is empty; no unit statement or step is bypassed.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
