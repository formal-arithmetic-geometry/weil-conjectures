## What changed

Restored `lean/Sheaf/Paper/TraceFormulaLocalFrobeniusOperator.lean` from its recorded
quarantine archive, retaining all ten attached definitions and every public import.
The assigned item is a zero-hole definition repair, not a theorem proof.

Inlined the local coefficient type in `finiteGlobalCompactStep` instead of making Lean
transform a dependent local `let`. The original whole-file profile measured 3 seconds
in let-to-have transformation; the repaired profile measured 3.57 milliseconds.
Explicitly stated the existing result types of `finiteLocalFibre`, `finiteLocalRho`,
and `finiteGlobalCompactSections`, with the same derived-category localization universes.
Later composites respect local irreducibility of the completed constructions, and
elaboration now respects transparency. The local attributes do not survive the namespace.
The actual functors, fixed-point identification, canonical comparison, Weil iterate,
compact-support transport, and repeated-transport recursion retain their formulas.

The profile of the repaired whole module compiled in 20.7 seconds, versus 27.0 seconds
for the original profiled definitions. Development profiling settings were then removed;
the final module compiled cleanly in 20.1 seconds with no warnings.
The unmodified archive also passed one compile in 21.9 seconds, so the historic timeout
is intermittent; this delivery performs a specific measured elaboration repair rather
than merely restoring an unchanged file.

Preserved the node's primary declaration, all ten declaration attachments, statement
dependencies, empty proof plan, and unit route; appended an implementation repair note
to its Lean record. Change record:
`coord/changes/D3-local-frobenius-operator-elaboration.md`.

All four archived direct consumers compiled unchanged in a scratch mirror against the
restored module: `Sheaf.Paper.CompletedStalkFrobeniusReduction`,
`Sheaf.Paper.FrobeniusOperatorCompactDescription`, `Sheaf.Paper.LocalFrobeniusConjugacy`,
and `Sheaf.TraceFormula.CompactDirectPowerTransportNormalization`. No consumer adaptation
is necessary. The artifact-producing batch reported 72.1 seconds for the item and
64.6--86.7 seconds for the unchanged consumers; the standalone final check reported
20.1 seconds. These are the tool's reported timings; no timeout option was changed.

## Proved and sorry left

Existing holes: 0. Holes closed: 0. Holes added: 0. Holes left: 0.
No theorem is split off. No definition contains a proof hole.
The ten definitions attached to `def-trf-frobenius-operators` are all retained:
`finiteLocalSections`, `finiteLocalFibre`, `finiteLocalRho`, `finiteLocalFrobenius`,
`finiteGlobalCompactSections`, `finiteGlobalCompactStep`, `finiteGlobalRepeatedTransport`,
`finiteGlobalComparedTransport`, `finiteGlobalFrobenius`, and
`finiteGlobalFrobeniusCohomology`, all in
`WeilConjectures.TraceFormulaCoefficientConventions`.

## No longer needed

None. No import, declaration, node, or module is pruned or withdrawn.
In particular, zero live importers results from quarantine and does not justify
withdrawal: the four archived direct consumers and the DAG parents still use the item.
The repository and Mathlib searches found no replacement for the actual finite-coefficient
operator construction; the recorded canonical transports and comparisons remain in use.

## Where the brief, the DAG or earlier work was wrong

The item has no `sorry`; its current rework row assigns the compile-time definition repair.
Its missing live source is explicitly quarantined, not withdrawn. The archived source
and its existing Lean attachment have therefore been restored rather than replaced
by an empty module. The repaired definition is definitionally equal to the archived
construction after substitution of the coefficient type alias; no mathematical
statement or source-library declaration is changed.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
