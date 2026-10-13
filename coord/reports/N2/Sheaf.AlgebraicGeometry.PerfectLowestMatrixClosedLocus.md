## What changed

Proved `AlgebraicGeometry.Scheme.exists_perfectLowestMatrixClosedLocus` without changing
its statement or its public imports. The proof reduces the problem to a local matrix
chart at each point, proves source locality of the cohomology rank condition, and
applies a fully proved gluing theorem.

Added `Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts`, containing the strictly local
matrix construction obligation, and `Sheaf.AlgebraicGeometry.LocalClosedLocusGluing`,
containing the proved generic theorem `exists_closedLocus_of_local_charts`.
The latter constructs scheme gluing data explicitly, checks its cocycle, identifies
the local representatives with target-open pullbacks, proves closed immersion and
local finite presentation by target locality, and glues local factors.

The item's three proved private helpers identify derived pullback cohomology after
source-open restriction with ordinary restriction, preserve fixed-rank finite local
freeness under restriction, and recover it from a pointwise open cover. They use
`DerivedPullbackComposition`, `DerivedOpenPullbackHomology` and the existing module
restriction/locality lemmas. No arbitrary base-change stability of the single
cohomology condition is assumed.

Updated the item's DAG proof and added nodes for both new theorems. No existing
statement, definition, target, unit realization or module interface was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_perfectLowestMatrixClosedLocus`
(node `lem-sc-perfect-lowest-matrix-closed-locus`).

Added one hole:
`AlgebraicGeometry.Scheme.exists_perfectLowestMatrixCharts`
(node `lem-sc-perfect-lowest-matrix-charts`, module `PerfectLowestMatrixCharts`).
Its proof is exactly `by sorry`; its docstring and node give the complete local
matrix argument, including ranks zero and smaller than r and the empty source.
This is a decomposition: one original hole closed, one strictly local hole added;
net hole reduction is zero. The global theorem still depends on this local hole.

`AlgebraicGeometry.Scheme.exists_closedLocus_of_local_charts`
(node `lem-sc-local-closed-locus-gluing`) is proved entirely from Mathlib.
The item contains no remaining direct `sorry`; there are no other added holes.

The three delivered modules compile together without warnings using `lcompile.py --all`.
The delivery dry run additionally checks every declaration with the project's axiom probe.

## No longer needed

Removed the direct proof imports `PerfectFiniteFreeResidueModel`, `PerfectJumpLoci`
and `FlatComplexDerivedPullback` from the item. The residue model and flat-complex
pullback remain mathematical dependencies of the local matrix-chart obligation;
this is movement of work to the local step, not a claim to have pruned those arguments.

`lem-sc-perfect-jump-loci` / `Sheaf.AlgebraicGeometry.PerfectJumpLoci` is no longer
needed for this node's argument: use the prescribed residue model at every point,
including points whose lowest rank is smaller than r. Padding an injective free map
with zero target coordinates rules out a rank-r kernel in that case, without upper
semicontinuity. Other nodes may still require jump loci.

The parent no longer directly uses `lem-sc-perfect-finite-free-residue-model`,
`lem-sc-square-injective-free-map-dual-coker-zero`,
`lem-pc-flat-complex-derived-pullback` or
`lem-weil-pbc-quasi-coherent-ideal-closed-subscheme`; these remain in the local
matrix-chart node's proof plan and are not claimed as pruned mathematical work.
No public import of the existing item was removed. The two new modules use the
smaller `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` import for their statements.

## Where the brief, the DAG or earlier work was wrong

The original ideal-to-closed-subscheme Mathlib leaf constructs a closed subscheme
from an already compatible quasi-coherent ideal; it does not itself supply the
representability comparison maps or their gluing. The delivery proves that missing
gluing argument directly using `Scheme.GlueData` and open-cover morphism gluing.

The source checked was Stacks Tag 0BDL, specifically the single-pullback criterion
on the rank-bound open, the local matrix calculation and the final gluing paragraph.
The statement is valid as written; no statement correction is proposed.
The unit's route is unchanged.

The existing `LocalImmersionLocus` was also checked. It requires stability under
arbitrary base change and concludes only immersion, so its interface does not supply
the closed, locally finitely presented conclusion needed here. The new gluing theorem
requires only source-open restriction stability and proves the stronger conclusion
from local closed, locally finitely presented charts.

Edge cases: the gluing proof covers empty target and source schemes without nonempty
assumptions; locality forces the predicate on the empty source. No quasi-compactness
or finite target cover is required. The matrix-chart plan covers r=0 (a zero first
term), smaller rank (an empty local locus) and a>b (Tor amplitude forces vanishing).

A read-only DAG audit also encountered the pre-existing cycle
`lem-pc-cycle-pullback-tower-comparison-stage3` -> `new-tower-comparison-first` ->
`lem-pc-cycle-pullback-tower-comparison-stage3` in the repository's dependency graph.
These nodes are outside this delivery and need maintainer attention. Checking each
edge of the three delivered node records found no cycle involving a delivered node.
The Lean import-cycle check and compilation pass.

## New nodes

`lem-sc-perfect-lowest-matrix-charts`:
`lean/Sheaf/AlgebraicGeometry/PerfectLowestMatrixCharts.lean` states local closed
finite-presentation representatives at each point of the rank-bound open. It carries
only the matrix-chart construction and kernel criterion, without global gluing.
LeanSearch was unavailable; LeanFinder, source grep and blueprint searches found no
exact existing theorem. The source and complete local proof are in its node/docstring.

`lem-sc-local-closed-locus-gluing`:
`lean/Sheaf/AlgebraicGeometry/LocalClosedLocusGluing.lean` proves gluing of local closed
finite-presentation representatives for an open-restriction-stable, source-local
predicate. It has no perfect-complex hypotheses and no `sorry`. The explicit proof
fills the details omitted in the source's gluing paragraph. Searches found Mathlib
scheme gluing and morphism gluing APIs, which the proof uses, but no theorem with
this interface. No change records or forced adaptations are required.

## Second reading by N2

1. **Unchanged interfaces: PASS.** Compared the item with the repository by `diff`.
   Its existing theorem signature is byte-for-byte identical; its docstring and
   public imports are unchanged. The differences are proof imports, three proved
   private helpers, and the proof body. The other two modules and their declarations
   are new. No definitions, target statements, change records or forced adaptations
   are introduced.
2. **Proof and trust: PASS, with the stated local obligation still open.** Independently
   compiled all three modules through `lcompile.py --all`, without errors or warnings.
   Read the full gluing proof, including transition lifts, monomorphism cancellation,
   cocycle, target-open pullback comparison, target locality, and source-cover gluing.
   Read the three homology/restriction helpers and the final application. A scratch
   copy with `#print axioms` showed only `propext`, `Classical.choice`, `Quot.sound`
   for `exists_closedLocus_of_local_charts`, and those plus `sorryAx` for the original
   theorem and `exists_perfectLowestMatrixCharts`. The scratch copy was removed.
   The only delivered `sorry` is the entire proof of the named chart theorem; there
   are no definitions with postponed data or forbidden declarations. Existential
   choices in the gluing proof come from its hypotheses and proved lifting claims.
3. **Split statement: PASS as a decomposition.** Checked the chart statement and
   its complete proof plan against [0BDL](https://stacks.math.columbia.edu/tag/0BDL),
   [0BCD](https://stacks.math.columbia.edu/tag/0BCD), and
   [0EWY](https://stacks.math.columbia.edu/tag/0EWY). A finite-free residue model at a
   point of rank s<r also excludes a rank-r kernel throughout that chart: pad a
   putative injection R^r -> R^s by zero target coordinates and use the transpose
   injectivity criterion over a nonzero affine source ring. At r=0 the first term
   is zero and the chart is the whole neighbourhood. Empty sources satisfy both
   sides; an empty target has no chart obligations. For a>b all fibre terms vanish,
   giving the whole chart for r=0 and the empty chart otherwise. The generic gluing
   theorem handles empty schemes using its possibly empty point-indexed covers.
   The chart obligation excludes global gluing, which is proved separately, so it
   is strictly a local part of the original argument, not a renamed global theorem.
   Additional LeanFinder queries used the words "representable closed subfunctor"
   and "Tor amplitude ... kernel of first differential"; Loogle searched
   `AlgebraicGeometry.IsClosedImmersion`; grep searched closed loci, kernels and
   charts in both library roots. Found general representability/gluing APIs and
   module-kernel lemmas, but no exact chart theorem or shorter direct route. This
   local construction cannot be closed by a short application of those results.
4. **Top-down route and pruning: PASS.** The final proof closes global gluing and
   source locality before leaving the local matrix construction open. All added
   imports used only in proofs are plain imports. Statement imports of the two new
   modules supply their signatures; gluing uses Mathlib directly. Compared all five
   old proof dependencies against the report: jump loci are bypassed, and the other
   four move to the local chart's mathematical proof plan. Their absence from the
   completed parent proof is explicitly recorded, without claiming they are proved.
   `dag/units/sk-prop-av-cube.json` has empty `realized.statement` and step lists;
   this delivery changes neither it nor its general-cube route. Net direct holes
   closed minus holes added is zero; this remains a decomposition, not a completed
   proof of the original theorem.
5. **Node agreement: PASS after record repair.** Checked the parent node's unchanged
   statement and updated proof steps against the Lean proof and its five dependencies.
   Checked both new nodes' source, statement dependencies, proof-step dependency
   unions, provenance, searches, status, creation, blueprint, chapter, unit and Lean
   records. The gluing node records Mathlib scheme and morphism gluing; the local node
   records the residue-model/matrix construction. Replaced the condensed new-node
   `lean.statement` fields by the exact multiline theorem signatures from the files.

Second-reading changes: corrected the two new nodes' verbatim signature records and
explicitly named `lem-sc-perfect-finite-free-residue-model` among the parent's removed
proof dependencies. No Lean proof or interface required repair. Appended this review.
