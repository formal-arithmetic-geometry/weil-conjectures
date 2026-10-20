## What changed

Withdrew the unused Sheaf.AlgebraicGeometry.OpenCoverRestrictionExact module under
brief step 8d. The theorem already has a complete proof in the adopted source module
WeilConjectures.AlgebraicGeometry.OpenCoverRestrictionExact. Attached node
lem-r4-open-cover-restriction-exact to that existing declaration and corrected the
proof text's import location. No adopted source file or mathematical statement changes.

Change record: coord/changes/r9-retire-open-cover-restriction-exact.md.

Validation: the original assigned module compiled in 3.8 seconds. A separate server
probe imported the source theorem and its existing KoszulRestrictionZeroBase consumer;
it compiled in 1.6 seconds and printed the theorem's axioms as exactly propext,
Classical.choice, and Quot.sound. The probe is not part of the packet.
The proof covers arbitrary index universes, including the empty cover, using sheaf
separation for the vanishing homology object. Read the source Stacks modules.tex,
lemma-abelian (Tag 01AG), and the unit record sk-thm-picard-duality: no unit step changes.

## Proved and sorry left

Actual initial hole count: zero. Holes closed: none (0 of 0). Holes added: none.
No sorry remains in any delivered module. No split-off theorem is introduced.
AlgebraicGeometry.exactAt_over_of_open_cover was already proved, with only standard
axioms, in the adopted source module; this delivery does not claim credit for that proof.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.OpenCoverRestrictionExact: no library module imports it.
Its imports Sheaf.Paper.DerivedHomMayerVietoris,
Mathlib.AlgebraicGeometry.Modules.Sheaf,
Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex, and
Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing disappear with that unused copy.
Those dependencies remain available where the retained source theorem needs them.
No mathematical dependency node is pruned: lem-r4-open-cover-restriction-exact remains
attached to the same theorem in the source module, which the existing source
KoszulRestrictionZeroBase consumer already uses. No source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished obligation, but coord/queue.tsv lists
this item as a zero-hole retirement with one consumer. Its current module has no
importers and has a proved adopted-source twin. The DAG still pointed to the unused
Sheaf copy. The retirement inventory lists this copy as waiting for a later wave
because a consumer was pending; the current source search and downstream check
establish that it now has no consumers. This packet completes that retirement. No previous proof obligation
is split or passed on again. Followed the prescribed shortest-route search through
msearch leanfinder, loogle, and grep, plus local searches in both library roots.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
