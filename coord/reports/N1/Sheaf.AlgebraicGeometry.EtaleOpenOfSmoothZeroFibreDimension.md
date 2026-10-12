## What changed

Proved `AlgebraicGeometry.exists_etale_open_of_smooth_of_fibre_dimension_zero` with its
statement unchanged. Replaced the two proof imports for differential modules with
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Updated the item's DAG proof,
proof dependencies and proof origin to the implemented route.

The existing source theorem `Smooth.exists_smoothOfRelativeDimension_resLE` supplies a chart
of relative dimension `d` inside the given open U. Transporting its source open into X produces
V ≤ U containing x. Restrict the original fibre to V and use base change stability and
`topologicalKrullDimAt_eq_of_smoothOfRelativeDimension` to compute its dimension as d.
Open-subspace invariance and the given hypothesis force d = 0. Mathlib's
`Etale.iff_smoothOfRelativeDimension_zero` then gives the required étaleness.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_etale_open_of_smooth_of_fibre_dimension_zero`
(node `lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension`).
There are no remaining sorries in the item and no holes added elsewhere. No decomposition.
The single-file compile passed without warnings; the delivery dry run checks declaration axioms.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`
  (`lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`).
- `Sheaf.AlgebraicGeometry.SmoothZeroDifferentialsAffineOpenEtale`
  (`lem-weil-pbc-smooth-zero-differentials-affine-open-etale`).

The differential-module route below these nodes is unnecessary for this proof, including
`lem-weil-pbc-standard-smooth-kahler-basis`, `def-weil-pbc-kahler-differentials`,
`lem-weil-pbc-affine-open-spec-points`,
`lem-weil-pbc-affine-opens-induced-ring-map-spec-square`,
`lem-weil-pbc-spec-residue-field-identification`,
`lem-weil-pbc-morphism-from-spec-field`, `lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-standard-smooth-base-change`,
`lem-weil-pbc-standard-smooth-over-field-dimension-at-points`,
`lem-weil-pbc-morphism-factors-through-open-subscheme`,
`lem-weil-pbc-smooth-restrict-open-subschemes`,
`lem-weil-pbc-smooth-ring-map-iff-smooth-affine`, `def-weil-pbc-smooth-ring-map`,
`lem-weil-pbc-etale-ring-map-iff-etale-affine`, and
`lem-weil-pbc-etale-composition-cancellation`. These are pruning opportunities for this edge,
not a claim that no other target path reaches them. In particular this proof no longer imports
`Sheaf.RingTheory.StandardSmoothDimensionAtPoints` through the differential-rank lemma.

Retained the original public imports so the statement's exported interface is unchanged.
Retained fibre pullbacks, open immersions, smooth relative dimension, and open-subspace
invariance in the mathematical argument. No realized unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound but overlooks the existing source library's
relative-dimension charts and dimension calculation over fields. They remove both outstanding
differential lemmas from this proof. No statements or definitions needed correction.
The original declaration docstring describes that planned argument; the new DAG proof and
proof-body comment describe the alternative actually implemented.

## Second reading by N1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and proof-only imports changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; no definitions were added. Verdict: pass.
3. Checked the proof route and dependencies against the imported source-library declarations and searched the repository for duplicate declarations. The relative-dimension chart and fibre dimension route is a genuine reduction and the DAG node is present; no split-off statements were added. Verdict: pass.
4. Verified the shorter source-library route is used and the two differential proof imports are removed. The report lists the resulting pruning opportunities. The retained public imports preserve the exported interface. Verdict: pass.
5. Compared the DAG node's Lean record, proof steps, proof dependencies, and proof origin with the implementation. They agree, and the unit route remains represented by the item's node. Verdict: pass.

Changed only the proof, proof-only import, DAG proof metadata, and this second-reading report section; no statements or definitions were changed.
