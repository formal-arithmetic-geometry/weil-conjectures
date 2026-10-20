## What changed

Completed the listed retirement repair for
`Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups`, which was already
fully proved before this assignment. The module is listed in `deleted.txt`.
Switched its two current direct consumers to the upstream
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups` by changing
only private imports. All existing consumer signatures and proof bodies remain
verbatim; all source-library public imports and attributes are preserved.

Reattached `cor-galois-open-subgroups` to upstream `galois_openSubgroups` and its
pointed/realization lemmas. The node records the canonical equivalence between
its small fundamental-group model and Aut(fiber s), and the proved equivalence
between categorical and scheme connectedness. Conjugacy by a translated point
agrees with the old explicit conjugation formula. The node's mathematical
statement and its unit route are unchanged.

Preserved the rank conclusion missing from the twin's API in the new, fully
proved `FiberCardDegree` module. Its theorem
`AlgebraicGeometry.Scheme.FiniteEtale.isFiniteLocallyFreeOfDegree_index_stabilizer`
computes finite locally free degree as stabilizer index. Its private geometric
fibre comparison is extracted from the old proved helper, generalized to a
separably closed geometric field. The public theorem rewrites the index by
Mathlib orbit-stabilizer and applies that comparison. The lisse-trivialization
consumer imports this lemma for its existing rank/surjectivity proof plan.

Validation: the original item compiled in 3.5 seconds. Both consumers compiled
with only the twin import (4.2 and 8.4 seconds). The new degree module and both
final consumer versions compile individually through lcompile.py. The delivery
tool additionally probes declaration axioms. The dry run passed with CODEX review
classification (commit d3ca175fcc9). It noted a 60-second timeout of the appended
axiom probe on RealSheaves, while that module itself compiled successfully;
the tool accepts the packet and the merge reruns that probe. No theorem body in
RealSheaves changed. No global build or local Lake command was run.

Change record: `coord/changes/F6-retire-fundamental-group-open-subgroups.md`.

## Proved and sorry left

Original item holes: 0. Closed 0 of 0 original holes; added 0 holes;
0 obligations split off unfinished. This is a retirement/API-preservation repair,
not a new closure of the classification theorem.

The new public theorem
`AlgebraicGeometry.Scheme.FiniteEtale.isFiniteLocallyFreeOfDegree_index_stabilizer`
(node `lem-fet-geometric-fiber-degree`) and its private `degree_eq_fiber_card`
helper are proved, with no sorry. The classification remains proved upstream.

The adapted consumer files retain these pre-existing holes unchanged:

- `AlgebraicGeometry.exists_finite_etale_surjective_trivializing_lisse`
  (`fin2-lem-lisse-trivialized-finite-etale`).
- `AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`
  (`lem-zl-curve-testing-irreducibility`).
- `AlgebraicGeometry.WeilSheaf.IsReal.isMixed`
  (`thm-zl-real-mixed-by-curves`); its existing inline sorry is untouched.

## No longer needed

Pruned the duplicate module
`Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups` and replaced both
current imports of it by the official twin. Its public
`connected_cover_open_subgroups` name has no source callers. Its private
connectedness, pointed-isomorphism, open-stabilizer and coset-realization
helpers are supplied by upstream Connected/OpenSubgroups and are not duplicated.
The private degree comparison survives in `FiberCardDegree` because it is not
provided by the twin's fibre-cardinality conclusion.

The DAG node is not withdrawn: its parents still need the classification.
No unit statement, unit proof step, or parent mathematical dependency is pruned.
The quarantined `DenseOpenPiOneSurjective` parent has no Lean use of the old
name; it is retained verbatim with its attachment and dependencies. Its future
rework must switch its archived import to the twin; this instruction is recorded
in the classification node's `lean.note` and the change record. Restoring that
unrelated quarantined module is outside this retirement packet.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief did not identify this as a retirement. The precise
assignment is its row in `coord/retire-items.tsv`. The source has zero sorry,
not an unproved classification theorem.

That row describes the two modules as having the same statements. Their APIs
actually differ: the old bundled theorem includes scheme rank, whereas the
upstream theorem states fibre cardinality; their fundamental-group universe and
connectedness interfaces also differ. The new proved degree-index result and
the existing canonical comparisons preserve the original mathematical meaning.

One listed consumer is quarantined and absent from lean/. It was checked in its
archive and not silently discarded or replaced by an empty module. The two live
consumers only import the old module in their proof environment and do not call
its old theorem, so no consumer proof change is required.

The prior corrected conjugacy-class statement is retained: unpointed covers
classify conjugacy classes, pointed covers classify individual subgroups.

## New nodes

`lem-fet-geometric-fiber-degree` in `dag/nodes/sec-smooth-purity/` records the
fully proved finite locally free degree-index comparison in
`Sheaf.AlgebraicGeometry.FundamentalGroup.FiberCardDegree`. Its proof computes the
geometric fibre cardinality via algebra maps, uses base change and locally
constant rank, and then applies transitive orbit-stabilizer. This is the missing
rank part of the existing classification argument, not a restatement of the
whole classification. The private comparison allows disconnected/empty covers;
its final connected degree-index form uses a fibre point and transitivity.
Identity covers give degree and index 1; the empty-cover comparison gives 0.
LeanSearch, LeanFinder, valid Loogle, Mathlib grep, and source/blueprint duplicate
searches found no existing exact scheme-degree theorem. This adds no hole.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
