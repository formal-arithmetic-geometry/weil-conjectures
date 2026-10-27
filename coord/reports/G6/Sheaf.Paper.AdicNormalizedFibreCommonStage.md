## What changed

Reduced `AlgebraicGeometry.Scheme.AdicFibreComparison.adic_normalized_fibre_common_stage`
to three strictly smaller arguments: exact finite-stage representatives, normalized
fibre transport, and joint zero-map detection. The original theorem now proves the
other three joint tests. Zero objects are detected through their identities; monicity
and epicity are reflected by testing kernel inclusions and cokernel projections;
fibrewise exactness kills the mapped kernel-to-cokernel composite. Three proved private
generic lemmas carry the categorical cancellation and factorization argument.

Moved the original two data records into the publicly reexported
`AdicNormalizedFibreCommonStageData`. Its `CommonStageFibreTransport` is the subset of
the original record containing the point and comparison fields, before all detection
and finite-stage-exactness fields. Four named irreducible propositions contain the
unchanged long comparison equations. This prevents repeated expansion of their functor
types in generated record declarations. The original theorem's hypotheses, universes
and conclusion, and the mathematical content of the data, are unchanged. No other
existing module uses either record; `tools/downstream.py --uses` confirms this.

The original interface copy timed out. Profiling localized repeated kernel checks and
generated recursors in the long comparison records. Naming the equations and sharing
the transport record allowed the data module to compile. The generic detection proofs
also keep category-generic cancellation separate from the large concrete common-heart
types. This refactor was for the repeated type expansion; the three mathematical
lemmas are split by the actual argument, not to evade the file time limit.

## Proved and sorry left

Original hole closed by reduction:
`AlgebraicGeometry.Scheme.AdicFibreComparison.adic_normalized_fibre_common_stage`.
Original count: 1. Remaining direct holes in the item: 0.
This is a decomposition, not a claim of a sorry-free proof: three lower holes are added.

- `AlgebraicGeometry.Scheme.AdicFibreComparison.common_stage_heart_exactness`
  (`lem-per-common-stage-heart-exactness`, module `Sheaf.Paper.AdicCommonStageHeartExactness`).
- `AlgebraicGeometry.Scheme.AdicFibreComparison.common_stage_fibre_transport`
  (`lem-per-common-stage-fibre-transport`, module `Sheaf.Paper.AdicCommonStageFibreTransport`).
- `AlgebraicGeometry.Scheme.AdicFibreComparison.common_stage_fibre_zero_map`
  (`lem-per-common-stage-fibre-zero-map`, module `Sheaf.Paper.AdicCommonStageFibreZeroMap`).

Each lower statement has its source, complete proof in words and DAG node. None repeats
the original theorem: heart exactness mentions no fibre family, transport supplies no
joint detection, and zero-map detection quantifies any common family with finite-stage
comparisons and proves only that one test. The remaining tests are proved in the item.
The data module contains no `sorry`, no chosen arbitrary witness and no new axiom.

## No longer needed

No mathematical dependency or module is globally pruned. All of the old plan's
geometric dependencies are still needed in the lower arguments. The item's former
private proof imports of `AdicNormalizedFibreExactness`, `PbcVerdierAxioms`,
`PbcCommonStageCones`, `CommonStageCalculus`, and
`WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology` are no longer direct
proof imports of the item: the finite geometry is isolated in the lower lemmas.
The original public imports are available through the public data reexport.
The three new lemma modules import only the data needed for their statements; planned
proof-dependency modules are recorded on their nodes for future proof work.
No source-library declaration or import is removed.

## Where the brief, the DAG or earlier work was wrong

The plan's kernel/cokernel/homology detection step admits a shorter formal assembly.
Joint zero-map detection alone reflects mono, epi and exactness: mapped universal
factorizations suffice, without separately proving preservation of each defect object
in the top-level detection argument. The stronger preservation assertions themselves
remain part of heart exactness, as the original statement requires.

Read BS Proposition 6.8.14 and Remark 6.8.15 in the supplied PDF (pages 61–62).
The new natural-language proofs are the parent node's explicit formal assembly of
those results, not a claim that BS prints each separate interface verbatim. Read the
unit `sk-p-dl-a1-perverse`; none of its realized statement or proof steps is bypassed.
Checked empty geometric-point families, zero arrows, zero objects, identity transitions,
arbitrary independent universes, and finite complexes with empty index type. In the
empty-family case the zero-map hypothesis forces all arrows zero; the generic proofs
therefore remain valid. No finiteness over Omega is assumed beyond the original data.

## New nodes

`def-per-common-stage-fibre-descent-interfaces` owns the moved interfaces and named
comparison propositions, with their exact equations. These are actual data definitions
and contain no holes.

`lem-per-common-stage-heart-exactness` isolates old steps 1, 2, 5, 6 and 8, including
finite complexes and exact representatives. It introduces no fibre or comparison data.

`lem-per-common-stage-fibre-transport` isolates old steps 3, 4, 7 and 10. It assumes
heart exactness and descends normalized fibres and scalar/pullback comparisons, with
all original normalization equations retained.

`lem-per-common-stage-fibre-zero-map` isolates only the zero-map part of old step 9,
using finite heart presentations and faithful scalar extension. The top-level proof
supplies every other detection assertion.

Change record: `coord/changes/G6-common-stage-fibre-descent-interfaces.md`.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
