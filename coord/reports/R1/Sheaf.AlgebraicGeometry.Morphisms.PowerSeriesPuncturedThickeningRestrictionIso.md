## What changed

Proved `AlgebraicGeometry.Scheme.isIso_powerSeries_punctured_thickening_restriction`
with its original signature and public imports unchanged. Apply the existing module-sheaf
Hartogs theorem to the structure module of the quotient thickening, then transport the ring
restriction isomorphism through the canonical pullback/open comparison and compose with
`ΓSpecIso.inv`.

Added two fully proved modules: `PowerSeriesTruncatedFlat` constructs the finite monomial
linear equivalence using the existing coefficient criterion; `PowerSeriesThickeningBoundaryDepth`
uses primality of the contracted quotient prime and the flat local depth formula to supply
Hartogs's boundary hypothesis. Updated all three DAG proof records. The private unit-stalk
and depth-equivalence helpers are adapted from the proved helpers in
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteHomExtension`; that whole module is not imported.

The unit route is retained: this is the finite-index scalar calculation of Stacks 0EY9,
with its depth-two Hartogs input. The coefficient and depth-formula results from other units
are generic tools. Read the official Stacks pages for Tags 0EY9, 0E9I and 0337.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.isIso_powerSeries_punctured_thickening_restriction`
(node `lem-sbc-power-series-punctured-thickening-restriction-iso`).

Also proved, without adding holes:
`MvPowerSeries.truncated_constants_flat` (node `lem-sbc-power-series-truncated-flat`) and
`AlgebraicGeometry.Scheme.powerSeries_thickening_boundary_depth`
(node `lem-sbc-power-series-thickening-boundary-depth`). All private helpers are proved.
No `sorry` remains in any delivered module. Holes closed: 1; holes added: 0.
The supplied Hartogs and flat-depth results are used as existing declarations; this does
not assert that their whole transitive import closures are free of existing holes.

All three modules compile in dependency order via `lcompile.py --all`, without warnings.
The flatness lemma needs neither locality nor Noetherianity and includes d=0, n=0, zero rings
and nilpotent coefficients. The boundary theorem also includes d=0 and n=0; the original
target keeps its positive-d hypothesis unchanged.

## No longer needed

No original import or proof-dependency node was removed. The original Hartogs dependency
is used. Removed the exploratory proof imports `Mathlib.LinearAlgebra.Pi` from the flatness
module and `Mathlib.RingTheory.MvPowerSeries.Equiv` from the target: their necessary declarations
are already available through retained imports. No existing module or node is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan's second step was unstated glue rather than an available canonical ring
comparison. The delivery supplies it: identify the module and ring restriction functions,
and use the canonical pullback/open isomorphism. The monomial calculation follows from the
already proved combined-ideal coefficient criterion and requires no new hole. No existing
mathematical statement was corrected.

LeanSearch returned Internal Server Error. Unavailable searches are recorded without an
absence verdict, alongside successful LeanFinder, Loogle and pinned-source grep searches.
The blueprint ancestor utility cannot follow the old node's module-valued `created.item`;
the new nodes record the actual ancestor `sbc-thm-spreading-finite-etale-galois` and the
intermediate nodes already identified in the parent's ancestry records.

## New nodes

`lem-sbc-power-series-truncated-flat`, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/PowerSeriesTruncatedFlat.lean`, states and proves
flatness of the constants map to the total-degree quotient over any commutative ring.
It uses `lem-weil-pbc-power-series-kernels` and
`lem-weil-pbc-power-series-combined-ideal-coefficients` as generic algebra tools.

`lem-sbc-power-series-thickening-boundary-depth`, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/PowerSeriesThickeningBoundaryDepth.lean`, states
and proves the stalk-depth bound needed for Hartogs. It uses the preceding flatness lemma
and `lem-weil-pbc-flat-local-depth-formula` as a generic local-ring tool.
No change record is required: no existing public interface or statement was changed.

## Second reading by R1

1. I compared the delivered target module with the repository version. The target theorem signature and its public imports are byte-for-byte unchanged; the added imports are proof-only or introduce the two new helper modules. Verdict: unchanged interface and no accidental hypothesis or conclusion change.
2. I compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. The files contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proofs use only the permitted existing results and ordinary Lean constructions.
3. I checked the two split-off declarations against the source statements and searched the library and available LeanFinder/Loogle/grep results. `truncated_constants_flat` is the finite monomial flatness calculation, and `powerSeries_thickening_boundary_depth` is the stalk depth consequence; both are true, strictly simpler than the target, and have complete docstrings and matching DAG nodes. No duplicate declaration was found.
4. I checked the proof from the target downward. It uses the boundary-depth theorem, the existing depth-two Hartogs theorem, the canonical pullback comparison, and `ΓSpecIso.inv`; the unit route through the finite-index calculation and Hartogs is retained. The flatness and boundary modules retain only imports used by their statements or proofs, and the report's pruning list records the removed exploratory imports.
5. I checked the three DAG records: declarations, statements, proof steps, proof dependencies, origins, units, chapters, and source references agree with the Lean files. The target node is proved with the original statement; the two new nodes are marked split and describe exactly the intermediate results.

I changed only this report section after the worker delivery; no Lean proof or statement was altered during second reading.
