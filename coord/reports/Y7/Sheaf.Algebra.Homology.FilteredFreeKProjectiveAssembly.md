## What changed

Retired `Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly` in favor of the already
proved `WeilConjectures.Algebra.Homology.FilteredFreeKProjectiveAssembly`. The queue marks
this assignment `retire`; it has zero holes, rather than an outstanding proof obligation.

The sole consumer, `Sheaf.Algebra.Homology.FilteredFreeKProjective`, imports the upstream
twin and applies its direct `P.IsKProjective` conclusion in
`CochainComplex.isKProjective_of_filtered_free_telescope`. This replaces unpacking an
isomorphic model and transporting K-projectivity. All its declaration signatures,
definitions, public imports and other proofs remain unchanged. No upstream file changes.

The existing node `lem-pc-filtered-free-kprojective-assembly` points to the upstream
declaration, with its exact signature and the equivalence explained in `lean.note`.
Its mathematical statement and both proof dependencies are unchanged.

Read the local Stacks `dga.tex`, `lemma-property-P-sequence` and
`lemma-property-P-K-projective` (Tags 09KL--09KM), both telescope assembly modules, the
coproduct and degreewise-splitting declarations and nodes, and the consumer. Both assembly
variants have identical hypotheses, including carrier universes, zero initial stage,
monic inclusions, compatibility, exhaustion, degreewise retractions and K-projective
stages. Existence of an isomorphic K-projective complex is equivalent to K-projectivity
of P by Mathlib's `isKProjective_of_iso`; the upstream proof gives the latter directly.
Zero rings, zero filtrations and unbounded complexes are retained without restriction.
The unit record has no realized statement or steps bypassed by this retirement.

Validation: the original item compiled without errors or warnings. The adapted consumer
is checked through `lcompile.py` and the delivery tool's axiom probe and preflight.
Searches with `msearch.py`: leanfinder for exhaustive split filtrations, loogle for
`CochainComplex.isKProjective_of_iso`, and grep for `filtered_free_telescope_assembly`.
Targeted `rg` found the exact upstream assembly twin and its direct consumer.

Change record: `coord/changes/Y7-retire-filtered-free-kprojective-assembly.md`.

## Proved and sorry left

This is duplicate retirement, not a new proof or decomposition.
Original item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No declaration left with `sorry` in any delivered Lean file.
The upstream `CochainComplex.filtered_free_telescope_assembly` is already proved; the
consumer's `CochainComplex.isKProjective_of_filtered_free_telescope` now applies it
without any existential-model transport. No holes are removed by changing a statement.

## No longer needed

Pruned module: `Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly`, listed in
`deleted.txt`. Its sole consumer's import changes to
`WeilConjectures.Algebra.Homology.FilteredFreeKProjectiveAssembly`.

The withdrawn copy's private helper `isKProjective_of_degreewise_split` and redundant
public assembly declaration are no longer needed locally. Its public imports
`Mathlib.Algebra.Homology.HomotopyCategory.KProjective` and
`Mathlib.Algebra.Category.ModuleCat.Abelian`, and proof imports
`Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`,
`WeilConjectures.Algebra.Homology.CoproductKProjective` and
`WeilConjectures.Algebra.Homology.FilteredFreeTelescopeSplitting` remain used by the
upstream twin. They are not claimed as pruned modules.

No DAG node is deleted. Both `lem-pc-coproduct-kprojective` and
`lem-pc-filtered-free-telescope-splitting` are still needed by the upstream proof.
No further modules or proof dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an unfinished obligation split off five times, but
the current queue explicitly assigns retirement and the module already has zero holes.
The actual API difference is the upstream direct `P.IsKProjective` conclusion versus
the Sheaf existential isomorphic-model conclusion. Adapting the sole consumer resolves
this difference; no theorem or definition repair is necessary. The node's mathematical
statement remains equivalent to its new upstream attachment.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
