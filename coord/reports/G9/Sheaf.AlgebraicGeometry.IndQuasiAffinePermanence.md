## What changed

Proved `AlgebraicGeometry.indQuasiAffineProperty_permanence` in
`Sheaf.AlgebraicGeometry.IndQuasiAffinePermanence`, preserving its statement and the
`indQuasiAffineProperty` definition verbatim. Added only proved private helpers and private
instances. They identify the predicate with the affine-local property that every quasi-compact
source open is quasi-affine, prove its locality from the stated chart-descent theorem, and
prove its affine-base-change stability from the stated enlargement theorem. Mathlib's
`HasAffineProperty` API supplies arbitrary base change and affine-cover descent. For an affine
target, the union of two affine opens supplies the separated neighbourhood required by the
stated pair-neighbourhood theorem.

Replaced the two old proof imports by the three dependencies in the current DAG plan:
`QuasiCompactOpenQuasiAffineChartDescent`, `QcOpenPullbackQuasiAffineEnlargement`, and
`SeparatedAffinePairNeighbourhoods`. Updated the node's proof and dependency list to describe
this assembly. No statements, public imports, definitions, or downstream interfaces changed.

The item compiled through `lcompile.py` with exit code 0 and no Lean warnings.
Existing search results in `searches.jsonl` include LeanFinder, Loogle, and grep; there is no
existing Mathlib theorem stating the three ind-quasi-affine permanence clauses, but its generic
`HasAffineProperty` framework supplies the locality/base-change assembly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.indQuasiAffineProperty_permanence`
(node `lem-a1-ind-quasi-affine-permanence`). The item now has zero `sorry`; added zero holes
and split off zero statements. All added private helpers and instances have complete proofs.

The proof intentionally uses the existing stated declarations
`AlgebraicGeometry.isQuasiAffineHom_quasiCompact_open_of_affine_charts`,
`AlgebraicGeometry.qc_open_pullback_quasi_affine_enlargement`, and
`AlgebraicGeometry.Scheme.separated_of_affine_pair_neighbourhoods`.
Those declarations remain existing dependencies with their own holes; this packet does not
claim that the item's transitive axiom closure is sorry-free.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.QuasiAffineBaseChange` and
`Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality`: their uses are already encapsulated in
the stated enlargement and chart-descent dependencies. They remain transitively needed by
those dependencies, so no global module withdrawal is claimed.

Removed the direct node dependency `lem-a1-quasi-affine-target-locality`: the source-library
quasi-affine morphism API supplies the affine-target equivalence directly. Removed direct
`lem-weil-pbc-affine-opens-basis`: Mathlib's generic affine-property framework handles affine
refinement. Both remain used within the retained dependency proofs. Withdrew the stale
`tool_uses` entry `lem-trf-quasi-affine-base-change`; this theorem is used inside the enlargement
argument, not directly by the item. No modules are withdrawn and none are claimed globally
pruned. The unit route is retained; its realized statement/step lists are empty for this item.

## Where the brief, the DAG or earlier work was wrong

The original Lean file still imported the pre-split proof dependencies, whereas the current
node already supplies three separate statements for the substantive arguments. The delivery
uses those current declarations. No mathematical statement repair was necessary. Empty source,
empty cover, and empty quasi-compact opens are handled by the quantified dependencies and
Mathlib's cover API; no inhabitedness or nonemptiness hypotheses were introduced.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
